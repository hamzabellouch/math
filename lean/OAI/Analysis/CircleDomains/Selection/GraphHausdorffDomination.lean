import OAI.Analysis.CircleDomains.Topology.OpenGraphHausdorff
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-! Outer regularity turns the local graph-cover energy payment into
Hausdorff-measure domination and, in particular, preservation of null sets. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma graph_hausdorff_le_of_local_covers {A : Set GraphSpace}
    (μ : Measure GraphSpace) [μ.OuterRegular] (K : ℝ≥0∞) (hK : K ≠ ∞)
    (hlocal : ∀ s, 0 < s → ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s))) :
    (μH[2] : Measure GraphSpace) A ≤ 4096*K*μ A := by
  by_cases hK0 : K = 0
  · simpa only [hK0,mul_zero,zero_mul] using
      local_graph_hausdorff_le_open isOpen_univ (subset_univ A) μ K hlocal
  · have hc0 : (4096:ℝ≥0∞)*K ≠ 0 := mul_ne_zero (by norm_num) hK0
    have hct : (4096:ℝ≥0∞)*K ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hK
    rw [A.measure_eq_iInf_isOpen μ]
    simp_rw [ENNReal.mul_iInf_of_ne hc0 hct]
    exact le_iInf fun O => le_iInf fun hAO => le_iInf fun hO =>
      local_graph_hausdorff_le_open hO hAO μ K hlocal

lemma graph_hausdorff_zero_of_local_covers {A : Set GraphSpace}
    (μ : Measure GraphSpace) [μ.OuterRegular] (K : ℝ≥0∞) (hK : K ≠ ∞)
    (hlocal : ∀ s, 0 < s → ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s)))
    (hA : μ A = 0) : (μH[2] : Measure GraphSpace) A = 0 := by
  apply le_antisymm _ bot_le
  simpa only [bot_eq_zero,hA,mul_zero] using graph_hausdorff_le_of_local_covers μ K hK hlocal

end CircleDomainRigidity

end

end OAI
