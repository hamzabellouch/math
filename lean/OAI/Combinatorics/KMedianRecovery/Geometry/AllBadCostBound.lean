import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ExchangeAddNonempty

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma all_bad_cost_bound (F D S O : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F) (hcard : O.card ≤ S.card)
    (assign : V → V) (hassign : ∀ p ∈ D, assign p ∈ O) :
    cost D S ≤ (17/5:ℝ)*(∑ p ∈ D, dist p (assign p)) := by
  have hs := protected_swap_sum F D S O ∅ hS hSF hlocal hOF (by simpa using hcard)
    assign id (fun p hp => Or.inl (hassign p hp)) (by simp) (by simp)
  have he : (∑ p ∈ D, if assign p ∈ O then
        (1+2*(6/5:ℝ))*dist p (assign p)-connection S p else
        (6/5:ℝ)*(dist p (id (assign p))-connection S p)) =
      (17/5:ℝ)*(∑ p ∈ D, dist p (assign p))-cost D S := by
    rw [cost,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [hassign p hp,ite_true]
    ring
  rw [he] at hs
  linarith

lemma local_five_approx (F D S O : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
    (hSF : S ⊆ F) (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F)
    (hcard : O.card ≤ S.card) : cost D S ≤ 5*cost D O := by
  have hs := all_bad_cost_bound F D S O hS hSF hlocal hOF hcard (nearest O hO)
    (fun p _ => nearest_mem O hO p)
  simp only [nearest_distance] at hs
  change cost D S ≤ (17/5:ℝ)*cost D O at hs
  nlinarith [cost_nonneg D O]

lemma local_combined_cost_bound (F D S O : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
    (hSF : S ⊆ F) (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F)
    (hcard : O.card ≤ S.card) :
    (∑ p ∈ D, (connection S p + connection O p)) ≤ 6*cost D O := by
  have h := local_five_approx F D S O hS hO hSF hlocal hOF hcard
  rw [Finset.sum_add_distrib]
  change cost D S+cost D O ≤ 6*cost D O
  linarith

end MetricKMedianRecovery.LocalSearch

end OAI
