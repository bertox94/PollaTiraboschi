open util/boolean
open util/integer


sig RegUser{
	fiscalCode: one FiscalCode,
	age: one Int,
	position: one Position,
	heartbeat: one Int
}
--boundaries for age and heartbeat
{ age >= 0 and age <= 4 and heartbeat > 0 }

sig RegThirdParty{
	vat: one VAT,
	requests: set Request,
	dataset: one Dataset
}

sig Dataset{
	users: set RegUser,
	anon: set Position
}

--In order to simplify the model, these entities are not further specified.
sig FiscalCode, VAT, Position{}

sig Ambulance{
	patient: one SOSUser,
	destination: one Position
}

abstract sig Request{}

sig GroupRequest extends Request{
	ageSelector: one Int
}
--boundaries for the age discriminator, used to select individuals
{ ageSelector >= 0 and ageSelector <= 4 }


sig SingleRequest extends Request{
	userFC: one FiscalCode,
	accepted: one Bool
}

sig SOSUser extends RegUser{
	threshold: one Int
}
--
{ threshold > 0 }
	

lone sig InDanger{
	users: set SOSUser
}



--XXXXXXXXX
fun isItAnonymous [a: Int] : set RegUser{
	{ u: RegUser | u.age = a}
}
	
-------------------------------------------------------------------------------------------

--Two diffenrent users cannot have the same fiscal code.
fact fiscalCodeIsUnique{
	no disjoint u1, u2: RegUser | u1.fiscalCode = u2.fiscalCode
}

--Each fiscal code must be associated to a user.
fact noLoneFiscalCode{
	all f1: FiscalCode | some u1: RegUser | u1.fiscalCode = f1
}

--Two different Registered Third Party cannot have the same VAT.
fact thirdPartyIdIsUnique{
	no disjoint t1, t2:	 RegThirdParty | t1.vat = t2.vat
}

--Each VAT must be associated to a RTP.
fact noLoneVAT{
	all v1: VAT | some t1: RegThirdParty | t1.vat = v1
}

--Each position must be associated to a user.
fact noLonePosition{
	all p1: Position | some u1: RegUser | u1.position = p1
}

-----------------------------------------------------------------------------------------
--A RTP cannot send more than one request to the same user.
fact oneSingleRequestPerUserPerRTP{
	(all t1: RegThirdParty |
		no disjoint r1, r2: SingleRequest |
			r1 in t1.requests and r2 in t1.requests and r1.userFC = r2.userFC) and
	(no disjoint t1, t2: RegThirdParty |
		some r: Request |
			r in t1.requests and r in t2.requests)
}


--Two different RTP cannot have the same dataset
fact datasetIsUnique {
	no disjoint t1, t2: RegThirdParty |
		t1.dataset = t2.dataset
}

--Each dataset must be associated to a RTP.
fact noLoneDataset {
	all d1: Dataset | some t1: RegThirdParty | t1.dataset = d1
}

fact noLoneRequest {
	all r: Request | some t: RegThirdParty | r in t.requests
}

fact noDoubleGroupRequests {
	all t: RegThirdParty |
		no disjoint gr1, gr2: GroupRequest |	
			gr1 in t.requests and gr2 in t.requests and 
			gr1.ageSelector = gr2.ageSelector
}

/* A user is present in a RTP's dataset if and only if the said RTP has requested that individual
  for his/hers data and he/she has given consent */
fact inDatasetIffConsenting{
	all u: RegUser, t: RegThirdParty |
		u in t.dataset.users iff (some sr: SingleRequest |
			sr in t.requests and sr.userFC = u.fiscalCode and sr.accepted = True)
}

/* Anonymized users' data is present in a RTP's dataset if and only if the said RTP has
  issued a group request that grants users' anonymity */
fact inDatasetIffAnon{
	all t: RegThirdParty, u: RegUser |
		u.position in t.dataset.anon iff some gr : GroupRequest |
			(gr in t.requests and gr.ageSelector = u.age 
			and #isItAnonymous[gr.ageSelector] >= 1)
}
---------------------------------------------------------------------------------------

--A SOSUser is in danger if and only if his/hers heartbeat is below the threshold
fact inDangerIffBelowThreshold{
	all s: SOSUser | 
		(s.heartbeat < s.threshold iff s in InDanger.users)
}

--Each SOSUser in danger must have an ambulance sent to his/hers position
fact ambulanceInDanger{
	all u: SOSUser |
		u in InDanger.users implies some a: Ambulance | 
			a.patient = u
}

--No ambulance is dispatched without an emergency
fact ambulanceInDanger{
	all a: Ambulance |
		a.patient in InDanger.users
}

--Only one ambulance per user must be dispatched
fact noDoubledAmbulances{
	no disjoint a1, a2: Ambulance |
		a1.patient = a2.patient
}

--The destination of the ambulance must be the position oof the user in danger
fact ambulanceCorrectDestination{
	all a: Ambulance, u:SOSUser |
		a.patient = u implies a.destination = u.position
}

----------------------------------------------------------------------------------------------

/* If and only if a SOSUser's health parameters drop below his/hers threshold
  an ambulance is dispatched. */
assert ambulanceAlwaysWhenNeeded{
	(all u: SOSUser |
		u.heartbeat < u.threshold implies one a: Ambulance |
			(a.patient = u and a.destination = u.position)) and
	(all a: Ambulance |
		a.patient.heartbeat < a.patient.threshold)
}

assert singleRequestAcceptedCase{
	all u: RegUser, t: RegThirdParty, sr: SingleRequest |
		sr in t.requests and sr.userFC = u.fiscalCode and sr.accepted = True implies
			u in t.dataset.users
}

assert singleRequestDeniedCase{
	all u: RegUser, t: RegThirdParty, sr: SingleRequest |
		sr in t.requests and sr.userFC = u.fiscalCode and sr.accepted = False implies
			u not in t.dataset.users
}


pred show{
	#RegUser = 3
	#SOSUser = 2
	#InDanger.users = 2
}

pred groupRequest(gr: GroupRequest, t: RegThirdParty, u1, u2: RegUser, 
			p1, p2: Position, a: Int){
	u1.age = a
	u2.age = a
	gr.ageSelector = a
	gr in t.requests
	u1.position = p1
	u2.position = p2
	
	p1 in t.dataset.anon and p2 in t.dataset.anon
}

check ambulanceAlwaysWhenNeeded
		
check singleRequestAcceptedCase

check singleRequestDeniedCase

run groupRequest for 7 but 4 Int

run show for 8 but exactly 3 SingleRequest, exactly 2 GroupRequest, exactly 2 RegThirdParty


  
