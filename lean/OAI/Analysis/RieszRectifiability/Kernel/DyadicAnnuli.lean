import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def dyadicAnnulus {d : ℕ} (x : Ambient d) (ε : ℝ) (k : ℕ) : Set (Ambient d) :=
  {y | ε * 2 ^ k ≤ dist x y ∧ dist x y < ε * 2 ^ (k + 1)}

theorem dyadicAnnulus_measurable {d : ℕ} (x : Ambient d) (ε : ℝ) (k : ℕ) :
    MeasurableSet (dyadicAnnulus x ε k) := by
  exact (measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable).inter
    (measurableSet_lt (continuous_const.dist continuous_id).measurable measurable_const)

theorem dyadicAnnulus_subset_ball {d : ℕ} (x : Ambient d) (ε : ℝ) (k : ℕ) :
    dyadicAnnulus x ε k ⊆ ball x (ε * 2 ^ (k + 1)) := by
  intro y hy
  simpa only [mem_ball, dist_comm] using! hy.2

theorem exterior_subset_iUnion_dyadicAnnulus {d : ℕ} (x : Ambient d)
    (ε : ℝ) (hε : 0 < ε) :
    {y | ε < dist x y} ⊆ ⋃ k : ℕ, dyadicAnnulus x ε k := by
  intro y hy
  have hratio : 1 ≤ dist x y / ε := (le_div_iff₀ hε).2 (by simpa using! hy.le)
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near hratio (show (1 : ℝ) < 2 by norm_num)
  refine mem_iUnion.mpr ⟨k, ?_⟩
  exact ⟨by simpa [mul_comm] using! (le_div_iff₀ hε).mp hk₁,
    by simpa [mul_comm] using! (div_lt_iff₀ hε).mp hk₂⟩

theorem dyadicAnnulus_measure_lt_top {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    μ (dyadicAnnulus x ε k) < ∞ :=
  ((measure_mono (dyadicAnnulus_subset_ball x ε k)).trans
    (hg.2 x _ (by positivity))).trans_lt ENNReal.ofReal_lt_top

theorem inverseDistancePow_bound_on_annulus {d : ℕ} (p : ℕ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (y : Ambient d) (hy : y ∈ dyadicAnnulus x ε k) :
    ‖inverseDistancePow p x y‖ ≤ ((ε * 2 ^ k) ^ p)⁻¹ := by
  rw [Real.norm_of_nonneg (inverseDistancePow_nonneg p x y)]
  simpa only [inverseDistancePow, one_div] using!
    one_div_le_one_div_of_le (pow_pos (show 0 < ε * 2 ^ k by positivity) p)
      (pow_le_pow_left₀ (show 0 ≤ ε * 2 ^ k by positivity) hy.1 p)

theorem inverseDistancePow_integrableOn_annulus {d : ℕ} (n p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    IntegrableOn (inverseDistancePow p x) (dyadicAnnulus x ε k) μ := by
  apply Measure.integrableOn_of_bounded (dyadicAnnulus_measure_lt_top n C μ hg x ε hε k).ne
    (inverseDistancePow_measurable p x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (dyadicAnnulus_measurable x ε k)] with y hy
  exact inverseDistancePow_bound_on_annulus p x ε hε k y hy

end

end RieszRectifiability

end OAI
