import Mathlib
import OAI.Computability.QuantumFactoring.BitStackDivision

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def unaryDecodeStep (s : ℕ×ℕ) : ℕ×ℕ := if s.1=0 then s else (s.1-1,s.2+1)
lemma unaryDecodeStep_iterate (k : ℕ) (s : ℕ×ℕ) :
    (unaryDecodeStep^[k]) s=(s.1-k,s.2+min k s.1) := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih]
    unfold unaryDecodeStep
    split
    · rename_i hz
      apply Prod.ext <;> dsimp only <;> omega
    · rename_i hz
      apply Prod.ext <;> dsimp only <;> omega
namespace Procedure
noncomputable def unaryDecodeStepP : Procedure (prodCode Nat.bits unaryCode) (prodCode Nat.bits unaryCode)
    unaryDecodeStep := by
  let x:=first Nat.bits unaryCode
  let y:=second Nat.bits unaryCode
  let next:=(binarySub.comp (x.pair (Procedure.constant _ Nat.bits 1))).pair (unarySuccessor.comp y)
  exact (conditional (binaryZero.comp x) (identity _) next).congrFun (by
    intro s;unfold unaryDecodeStep;split <;> simp_all)
noncomputable def clippedUnary : Procedure (prodCode unaryCode Nat.bits) unaryCode (fun x=>min x.1 x.2) := by
  let rep:=unaryDecodeStepP.iterate Polynomial.X (by
    intro n s i hi
    rw [unaryDecodeStep_iterate]
    have hbits:=bits_length_mono (Nat.sub_le s.1 i)
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)
  let inp:=(first unaryCode Nat.bits).pair
    ((second unaryCode Nat.bits).pair (Procedure.constant _ unaryCode 0))
  exact ((second Nat.bits unaryCode).comp (rep.comp inp)).congrFun (by
    intro x;dsimp only [Function.comp_def];rw [unaryDecodeStep_iterate];simp)
noncomputable def boundedUnary {α : Type} {ea : α→List Bool} {f B : α→ℕ}
    (p : Procedure ea Nat.bits f) (b : Procedure ea unaryCode B) (h : ∀a,f a ≤ B a) :
    Procedure ea unaryCode f :=
  (clippedUnary.comp (b.pair p)).congrFun (by intro a;exact min_eq_right (h a))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
