import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGGateProcedure

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat
def notRef (a : Ref) : Ref := (a.1,!a.2)
def orGate (r : Graph) (a b : Ref) : Graph×Ref :=
  let s:=gate r (notRef a) (notRef b)
  (s.1,notRef s.2)
def xorGate (r : Graph) (a b : Ref) : Graph×Ref :=
  let s:=gate r a b
  let t:=gate s.1 (notRef a) (notRef b)
  gate t.1 (notRef s.2) (notRef t.2)
lemma or_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (orGate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkOrCached i) := by
  have hs:=gate_rel h (i.invert true true)
  simpa only [EPRel,orGate,AIG.mkOrCached,AIG.BinaryInput.invert,AIG.Ref.not,
    AIG.Ref.flip,Bool.true_xor,notRef] using And.intro hs.1 (congrArg notRef hs.2)
lemma xor_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (xorGate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkXorCached i) := by
  let s:=g.mkGateCached i
  let sr:=gate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)
  have hs : EPRel sr s:=gate_rel h i
  let i':=i.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) g i)
  let t:=s.aig.mkGateCached (i'.invert true true)
  let tr:=gate sr.1 (notRef (i.lhs.gate,i.lhs.invert)) (notRef (i.rhs.gate,i.rhs.invert))
  have ht : EPRel tr t := by
    simpa only [tr,t,i',notRef,AIG.BinaryInput.cast,AIG.BinaryInput.invert,
      AIG.Ref.cast,AIG.Ref.flip,Bool.true_xor] using gate_rel hs.1 (i'.invert true true)
  let a:=s.ref.cast (AIG.LawfulOperator.le_size (f:=AIG.mkGateCached) s.aig (i'.invert true true))
  have hh:=gate_rel ht.1 (⟨a.not,t.ref.not⟩ : AIG.BinaryInput t.aig)
  have ha : (a.not.gate,a.not.invert)=notRef sr.2 := by
    simpa only [a,AIG.Ref.cast,AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef]
      using congrArg notRef hs.2.symm
  have hb : (t.ref.not.gate,t.ref.not.invert)=notRef tr.2 := by
    simpa only [AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,notRef]
      using congrArg notRef ht.2.symm
  change EPRel (gate tr.1 (a.not.gate,a.not.invert) (t.ref.not.gate,t.ref.not.invert)) _ at hh
  rw [ha,hb] at hh
  exact hh

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def notRefP : Procedure refCode refCode notRef :=
  ((first Nat.bits boolCode).pair (boolNot.comp (second Nat.bits boolCode)))
noncomputable def orP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>orGate x.1 x.2.1 x.2.2) := by
  let r:=first graphCode keyCode
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let s:=gateP.comp (r.pair ((notRefP.comp a).pair (notRefP.comp b)))
  exact (((first graphCode refCode).comp s).pair
    (notRefP.comp ((second graphCode refCode).comp s))).congrFun (by intro x;rfl)
noncomputable def xorP : Procedure (prodCode graphCode keyCode) (prodCode graphCode refCode)
    (fun x=>xorGate x.1 x.2.1 x.2.2) := by
  let k:=second graphCode keyCode
  let a:=(first refCode refCode).comp k
  let b:=(second refCode refCode).comp k
  let s:=gateP
  let t:=gateP.comp (((first graphCode refCode).comp s).pair
    ((notRefP.comp a).pair (notRefP.comp b)))
  exact (gateP.comp (((first graphCode refCode).comp t).pair
    ((notRefP.comp ((second graphCode refCode).comp s)).pair
      (notRefP.comp ((second graphCode refCode).comp t))))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end



end OAI
