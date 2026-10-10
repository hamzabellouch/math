import Mathlib.Probability.CDF

namespace OAI

/-! # A median level for the local Poincare argument

Only the two half-mass inequalities are needed. The level is the lower
endpoint at which the cumulative distribution reaches one half.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

noncomputable section
namespace RegularPointCoordinates

theorem exists_probability_median (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ k : ℝ, (1 / 2 : ℝ≥0∞) ≤ μ (Iic k) ∧ (1 / 2 : ℝ≥0∞) ≤ μ (Ici k) := by
  let T : Set ℝ := {x | (1 / 2 : ℝ) ≤ cdf μ x}
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
  have hT : T.Nonempty := ⟨b, hb.le⟩
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  have hbelow : BddBelow T := ⟨a, fun x hx => by
    by_contra hax
    have := (monotone_cdf μ) (le_of_not_ge hax)
    exact (not_le.mpr ha) (hx.trans this)⟩
  let k : ℝ := sInf T
  have hright (x : ℝ) (hx : k < x) : (1 / 2 : ℝ) ≤ cdf μ x := by
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hT hx
    exact hy.trans ((monotone_cdf μ) hyx.le)
  have hleft (x : ℝ) (hx : x < k) : cdf μ x < (1 / 2 : ℝ) := by
    have hxnot : x ∉ T := notMem_of_lt_csInf hx hbelow
    exact lt_of_not_ge hxnot
  have hk : (1 / 2 : ℝ) ≤ cdf μ k := by
    apply ge_of_tendsto ((cdf μ).right_continuous k |>.mono Ioi_subset_Ici_self)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hright x hx
  have hlim : Function.leftLim (cdf μ) k ≤ (1 / 2 : ℝ) := by
    apply le_of_tendsto ((monotone_cdf μ).tendsto_leftLim k)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hleft x hx).le
  refine ⟨k, ?_, ?_⟩
  · rw [← ofReal_cdf]
    convert ENNReal.ofReal_le_ofReal hk using 1
    norm_num [ENNReal.ofReal_div_of_pos]
  · rw [← measure_cdf μ, (cdf μ).measure_Ici (tendsto_cdf_atTop μ)]
    have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
      norm_num [ENNReal.ofReal_div_of_pos]
    rw [hhalf]
    apply ENNReal.ofReal_le_ofReal
    linarith

end RegularPointCoordinates

end

end OAI
