import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGBoolean

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
abbrev Triple := Ref×Ref×Ref
def fullOut (r : Graph) (a b c : Ref) : Graph×Ref :=
  let s:=xorGate r a b
  xorGate s.1 s.2 c
def fullCarry (r : Graph) (a b c : Ref) : Graph×Ref :=
  let s:=xorGate r a b
  let t:=gate s.1 s.2 c
  let u:=gate t.1 a b
  orGate u.1 t.2 u.2
def full (r : Graph) (a b c : Ref) : Graph×(Ref×Ref) :=
  let o:=fullOut r a b c
  let k:=fullCarry o.1 a b c
  (k.1,(o.2,k.2))
lemma fullOut_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g)
    (i : FullAdderInput g) :
    EPRel (fullOut r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert))
      (mkFullAdderOut g i) := by
  let s:=g.mkXorCached ⟨i.lhs,i.rhs⟩
  have hs:=xor_rel h (⟨i.lhs,i.rhs⟩ : AIG.BinaryInput g)
  have hh:=xor_rel hs.1 (⟨s.ref,i.cin.cast (AIG.LawfulOperator.le_size (f:=AIG.mkXorCached) ..)⟩ :
    AIG.BinaryInput s.aig)
  change EPRel (xorGate _ (s.ref.gate,s.ref.invert) (i.cin.gate,i.cin.invert)) _ at hh
  rw [←hs.2] at hh
  exact hh
lemma fullCarry_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g)
    (i : FullAdderInput g) :
    EPRel (fullCarry r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert))
      (mkFullAdderCarry g i) := by
  let si : AIG.BinaryInput g:=⟨i.lhs,i.rhs⟩
  let s:=g.mkXorCached si
  have hs:=xor_rel h si
  let hsub:=AIG.LawfulOperator.le_size (f:=AIG.mkXorCached) g si
  let ti : AIG.BinaryInput s.aig:=⟨s.ref,i.cin.cast hsub⟩
  let t:=s.aig.mkAndCached ti
  have ht:=gate_rel hs.1 ti
  change EPRel (gate _ (s.ref.gate,s.ref.invert) (i.cin.gate,i.cin.invert)) t at ht
  rw [←hs.2] at ht
  let hlor:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) s.aig ti
  let ui : AIG.BinaryInput t.aig:=⟨(i.lhs.cast hsub).cast hlor,(i.rhs.cast hsub).cast hlor⟩
  let u:=t.aig.mkAndCached ui
  have hu:=gate_rel ht.1 ui
  change EPRel (gate _ (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert)) u at hu
  let hror:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) t.aig ui
  have hh:=or_rel hu.1 (⟨t.ref.cast hror,u.ref⟩ : AIG.BinaryInput u.aig)
  change EPRel (orGate _ (t.ref.gate,t.ref.invert) (u.ref.gate,u.ref.invert)) _ at hh
  rw [←ht.2,←hu.2] at hh
  exact hh
lemma full_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g)
    (i : FullAdderInput g) :
    Rel (full r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert)).1
      (mkFullAdder g i).aig ∧
    (full r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert) (i.cin.gate,i.cin.invert)).2 =
      (((mkFullAdder g i).out.gate,(mkFullAdder g i).out.invert),
        ((mkFullAdder g i).cout.gate,(mkFullAdder g i).cout.invert)) := by
  have ho:=fullOut_rel h i
  have hk:=fullCarry_rel ho.1 (i.cast (AIG.LawfulOperator.le_size (f:=mkFullAdderOut) g i))
  exact ⟨hk.1,congrArg₂ Prod.mk ho.2 hk.2⟩

end ExactQuantumFactoring.NativeAIG
end

end OAI
