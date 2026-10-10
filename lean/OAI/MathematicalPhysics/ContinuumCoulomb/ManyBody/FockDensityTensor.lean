import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockCoefficientNorm

namespace OAI

/-! Occupation-diagonal Coulomb tensors are density interactions with the
self term removed, as follows directly from the CAR. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

theorem twoBodyOperator_density {Q : ℕ} (V : Fin (Q+1) → Fin (Q+1) → ℂ) :
    twoBodyOperator (fun a b c d => if a=c ∧ b=d then V a b else 0) =
      (2:ℂ)⁻¹ • densityInteraction (fun a b => if a=b then 0 else V a b) := by
  unfold twoBodyOperator densityInteraction
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hi (c d : Fin (Q+1)) : (if a=c ∧ b=d then V a b else 0) =
      (if c=a then (if d=b then V a b else 0) else 0) := by
    by_cases hca : c=a <;> by_cases hdb : d=b <;> simp_all [eq_comm]
  simp only [hi,ite_smul,zero_smul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases hab : a=b
  · subst b
    simp [create_sq]
  · simp only [hab,ite_false,quartic_number a b hab]

end ContinuumCoulomb.HubbardGlobal

end

end OAI
