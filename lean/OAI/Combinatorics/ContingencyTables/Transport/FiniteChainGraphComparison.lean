import OAI.Combinatorics.ContingencyTables.Transport.FiniteChainWeightVariance

namespace OAI

/-! # Normalize a weighted graph inequality for its reversible chain -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators
open CommonBasesFPRAS

variable {X : Type*} [Fintype X] [Nonempty X]

lemma chain_poincare_of_weighted_graph (C : FiniteChain X) (w H : X → ℝ)
    (hw : ∀ x,0 < w x) (hπ : ∀ x,C.π x=w x/(∑ y,w y))
    (E K β : ℝ) (hK : 0 ≤ K) (hβ : 0 < β)
    (hv : variance w H ≤ K*E)
    (he : β/(2*(∑ x,w x))*E ≤ C.energy H) :
    C.variance H ≤ (2*K/β)*C.energy H := by
  have hZ : 0 < ∑ x,w x := Finset.sum_pos (fun x _ => hw x) Finset.univ_nonempty
  rw [chain_variance_eq C w H hπ]
  calc
    _ ≤ K*E/(∑ x,w x) := div_le_div_of_nonneg_right hv (le_of_lt hZ)
    _ = (2*K/β)*(β/(2*(∑ x,w x))*E) := by
      field_simp [ne_of_gt hβ,ne_of_gt hZ]
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

end ContingencyTables.FiniteExposureVariance

end OAI
