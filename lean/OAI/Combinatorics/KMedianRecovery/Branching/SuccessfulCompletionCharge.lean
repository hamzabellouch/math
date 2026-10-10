import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Cluster
import OAI.Combinatorics.KMedianRecovery.Recovery.SingleRadiusRatio

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma successful_completion_charge (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (J : Finset V) (I : ℝ) (hI : I ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hT : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign) :
    2*I + (∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, dist p (C.proxy o)) +
      (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
        (dist p o+(19/50:ℝ)*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) +
      (∑ o ∈ C.bad \ C.covered s, ∑ p ∈ cluster D C.assign o,
        if p ∈ J then dist p o else reference S Δ s p) ≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  have hA := C.covered_completion_sum hD (1/1000000) (19/50) (by norm_num) (by norm_num)
    s hs hP hm
  have hB := Finset.sum_le_sum (s := C.bad \ C.covered s) (fun o _ =>
    C.uncovered_completion_sum hD (1/1000000) Δ s hs hΔ J o)
  conv at hB => rhs; rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hpart := C.center_sum_partition s (C.correct_covered_subset hD (1/1000000) s hs)
    (clusterCost D C.assign)
  rw [comparisonCost_eq D O C.assign C.assigned] at hpart
  have hG := C.proxy_cost
  have hg0 : 0 ≤ ∑ o ∈ C.good, clusterCost D C.assign o :=
    Finset.sum_nonneg (fun o _ => clusterCost_nonneg _ _ o)
  have hb0 : 0 ≤ ∑ o ∈ C.bad \ C.covered s, clusterCost D C.assign o :=
    Finset.sum_nonneg (fun o _ => clusterCost_nonneg _ _ o)
  change (∑ o ∈ C.bad \ C.covered s, ∑ p ∈ C.near o, reference S Δ s p) ≤ _ at hT
  linarith

end MetricKMedianRecovery.Sampling.Comparison

end OAI
