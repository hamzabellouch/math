import OAI.Combinatorics.ContingencyTables.Transport.FiniteExposureVariance

namespace OAI

/-! # Normalizing a finite weighted variance -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators
open CommonBasesFPRAS

variable {X : Type*} [Fintype X]

lemma chain_variance_eq (C : FiniteChain X) (w H : X → ℝ)
    (hπ : ∀ x,C.π x=w x/(∑ y,w y)) :
    C.variance H=variance w H/(∑ x,w x) := by
  have hm : C.mean H=mean w H := by
    unfold FiniteChain.mean mean
    simp_rw [hπ,div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  unfold FiniteChain.variance FiniteChain.inner variance
  rw [hm]
  simp_rw [hπ]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

end ContingencyTables.FiniteExposureVariance

end OAI
