| package |
package := Package name: 'Contracts'.
package paxVersion: 1;
	basicComment: ''.


package classNames
	add: #CBClass;
	add: #CBMethod;
	add: #ContractBuilder;
	add: #ContractViolation;
	add: #Instrument;
	yourself.

package binaryGlobalNames: (Set new
	yourself).

package globalAliases: (Set new
	yourself).

package setPrerequisites: (IdentitySet new
	add: 'Object Arts\Dolphin\Base\Dolphin';
	yourself).

package!

"Class Definitions"!

Object subclass: #CBClass
	instanceVariableNames: 'invToAddSet invToRemoveSet parentInvSet methodDict'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Object subclass: #CBMethod
	instanceVariableNames: 'preAddSet preParentSet preRemoveSet postAddSet postParentSet postRemoveSet'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Object subclass: #ContractBuilder
	instanceVariableNames: 'cbcDict'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Error subclass: #ContractViolation
	instanceVariableNames: 'obj cond'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
ProtoObject subclass: #Instrument
	instanceVariableNames: 'contr obj'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!

"Global Aliases"!


"Loose Methods"!

"End of package definition"!

"Source Globals"!

"Classes"!

CBClass guid: (GUID fromString: '{AA5CF289-B320-4A84-93E6-5B66093399B4}')!
CBClass comment: ''!
!CBClass categoriesForClass!Unclassified! !
!CBClass methodsFor!

addInvariant: inv
	"Adds the invariant to the class representation."
	invToAddSet add: inv.
	(invToRemoveSet includes: inv) ifTrue: [invToRemoveSet remove: inv].!

initialize
	invToAddSet := IdentitySet new.
	invToRemoveSet := IdentitySet new.
	methodDict := Dictionary new.
	parentInvSet := IdentitySet new.!

invariants
	"Returns all the invariants for the given class."
	^(((parentInvSet copy) union: (invToAddSet copy)) difference: invToRemoveSet)!

method: meth
	^(methodDict at: meth ifAbsent: [methodDict at: meth put: (CBMethod new)])!

methods
	"Returns the dictionary with all methods for the class."
	^methodDict!

methods: meths
	"Setter for methods."
	methodDict := meths.!

parentInvariants: invs
	"Setter for parent invariants. Sets the parent invariants of this class to the given value (Set)."
	parentInvSet := invs.!

removeInvariant: inv
	"Removes the invariant from the class representation."
	invToRemoveSet add: inv.
	(invToAddSet includes: inv) ifTrue: [invToAddSet remove: inv].!

sum: other
	"Returns a new object representing a sum of invariants and method conditions for 2 class objects."
	|res mSum selfKeys otherKeys commonKeys|
	res := CBClass new.
	mSum := methodDict copy.
	mSum addAll: ((other methods) associations).
	selfKeys := methodDict keys.
	otherKeys := (other methods) keys.
	commonKeys := (selfKeys intersection: otherKeys).
	commonKeys do: [:key | mSum at: key put: ((methodDict at: key) sum: (other methods at: key))].
	res methods: mSum.
	res parentInvariants: self invariants.
	(other invariants) do: [:inv | res addInvariant: inv].
	^res! !
!CBClass categoriesFor: #addInvariant:!public! !
!CBClass categoriesFor: #initialize!public! !
!CBClass categoriesFor: #invariants!public! !
!CBClass categoriesFor: #method:!public! !
!CBClass categoriesFor: #methods!public! !
!CBClass categoriesFor: #methods:!public! !
!CBClass categoriesFor: #parentInvariants:!public! !
!CBClass categoriesFor: #removeInvariant:!public! !
!CBClass categoriesFor: #sum:!public! !

!CBClass class methodsFor!

new
	"Answer a new initialized instance."
	^super new initialize! !
!CBClass class categoriesFor: #new!public! !

CBMethod guid: (GUID fromString: '{A0B100F8-85ED-443D-B563-1BD230FD1FA7}')!
CBMethod comment: ''!
!CBMethod categoriesForClass!Unclassified! !
!CBMethod methodsFor!

addPostcondition: cond
	postAddSet add: cond.
	(postRemoveSet includes: cond) ifTrue: [postRemoveSet remove: cond].!

addPrecondition: cond
	preAddSet add: cond.
	(preRemoveSet includes: cond) ifTrue: [preRemoveSet remove: cond].!

initialize
	preParentSet := IdentitySet new.
	preAddSet := IdentitySet new.
	preRemoveSet := IdentitySet new.
	postParentSet := IdentitySet new.
	postAddSet := IdentitySet new.
	postRemoveSet := IdentitySet new.!

postConditions
	^(((postParentSet  copy) union: postAddSet) difference: postRemoveSet)!

postConditions: conditions
	postParentSet := conditions!

preConditions
	^(((preParentSet  copy) union: preAddSet) difference: preRemoveSet)!

preConditions: conditions
	preParentSet := conditions!

removePostcondition: cond
	postRemoveSet add: cond.
	(postAddSet includes: cond) ifTrue: [postAddSet remove: cond].!

removePrecondition: cond
	preRemoveSet add: cond.
	(preAddSet includes: cond) ifTrue: [preAddSet remove: cond].!

sum: other
	|res|
	res := CBMethod new.
	res preConditions: (self preConditions union: (other preConditions)).
	res postConditions: (self postConditions union: (other postConditions)).
	^res! !
!CBMethod categoriesFor: #addPostcondition:!public! !
!CBMethod categoriesFor: #addPrecondition:!public! !
!CBMethod categoriesFor: #initialize!public! !
!CBMethod categoriesFor: #postConditions!public! !
!CBMethod categoriesFor: #postConditions:!public! !
!CBMethod categoriesFor: #preConditions!public! !
!CBMethod categoriesFor: #preConditions:!public! !
!CBMethod categoriesFor: #removePostcondition:!public! !
!CBMethod categoriesFor: #removePrecondition:!public! !
!CBMethod categoriesFor: #sum:!public! !

!CBMethod class methodsFor!

new
	^super new initialize! !
!CBMethod class categoriesFor: #new!public! !

ContractBuilder guid: (GUID fromString: '{0198A206-47FA-4D11-9E67-939A143528C7}')!
ContractBuilder comment: ''!
!ContractBuilder categoriesForClass!Unclassified! !
!ContractBuilder methodsFor!

class: cls
	|b res|
	res := self getClass: cls.
	b := [:jmp :locC |  (locC = Object) ifFalse: [
		jmp value: jmp value: (locC superclass).
		res := res sum: (self getClass: locC).] ].
	b value: b value: cls.
	^(((self getClass: cls) parentInvariants: (res invariants)) methods: (res methods))!

contractFor: obj
	|orig invs meths|
	orig := self class: (obj class).
	invs := orig invariants copy.
	meths := orig methods copy.
	^(((CBClass new) parentInvariants: invs) methods: meths)
	!

getClass: cls
	"Extract or create a class representation object."
	^(cbcDict at: cls ifAbsent: [cbcDict at: cls put: (CBClass new)])!

initialize
	cbcDict := Dictionary new! !
!ContractBuilder categoriesFor: #class:!public! !
!ContractBuilder categoriesFor: #contractFor:!public! !
!ContractBuilder categoriesFor: #getClass:!private! !
!ContractBuilder categoriesFor: #initialize!public! !

!ContractBuilder class methodsFor!

new
	"Answer a new initialized instance."
	^super new initialize! !
!ContractBuilder class categoriesFor: #new!public! !

ContractViolation guid: (GUID fromString: '{B8E71392-E924-4A22-B9ED-9FBC0ACC1782}')!
ContractViolation comment: ''!
!ContractViolation categoriesForClass!Unclassified! !
!ContractViolation methodsFor!

condition
	^cond!

condition: aCond
	cond := aCond.!

isResumable
	^true!

object
	^obj!

object: aObj
	obj := aObj.
	! !
!ContractViolation categoriesFor: #condition!public! !
!ContractViolation categoriesFor: #condition:!public! !
!ContractViolation categoriesFor: #isResumable!public! !
!ContractViolation categoriesFor: #object!public! !
!ContractViolation categoriesFor: #object:!public! !

Instrument guid: (GUID fromString: '{EE67588F-9932-4A26-84ED-DCFBFB23B286}')!
Instrument comment: ''!
!Instrument categoriesForClass!Unclassified! !
!Instrument methodsFor!

contract: aContr object: aObj
	contr := aContr.
	obj := aObj.!

doesNotUnderstand: msg
	|invariants meth args res|
	invariants := contr invariants.
	self executeInvariants: invariants.
	meth := msg selector.
	args := (#(obj), msg arguments).
	((contr method: meth) preConditions) do: [:preCond |	
		(preCond valueWithArguments: args) ifFalse:  [((((PreconditionViolation new) object: obj) condition: preCond) method: meth) signal.].
	].
	res := msg forwardTo: obj.
	self executeInvariants: invariants.
	((contr method: meth) postConditions) do: [:postCond |	
		(postCond valueWithArguments: (args,#(res))) ifFalse:  [((((PostconditionViolation new) object: obj) condition: postCond) method: meth) signal.].
	].
	^res
	
	!

executeInvariants: invariants
	"Executes and checks if the invariants hold for the contract."
	invariants do: [:inv | 
		(inv value: obj) ifFalse: [(((InvariantViolation new) object: obj) condition: inv) signal]
	].! !
!Instrument categoriesFor: #contract:object:!public! !
!Instrument categoriesFor: #doesNotUnderstand:!public! !
!Instrument categoriesFor: #executeInvariants:!private! !

!Instrument class methodsFor!

contract: aContr on: aObj
	^(super new) contract: aContr object: aObj! !
!Instrument class categoriesFor: #contract:on:!public! !

"Binary Globals"!

