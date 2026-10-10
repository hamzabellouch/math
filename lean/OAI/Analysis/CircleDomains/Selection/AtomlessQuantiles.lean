import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Separated positive-mass intervals for an atomless real probability law.
These provide the four collar arcs in the crossing argument after choosing
a circle coordinate. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem atomless_cdf_leftLim (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (x : ℝ) : leftLim (cdf μ) x = cdf μ x := by
  have hz := (cdf μ).measure_singleton x
  rw [measure_cdf μ, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hz
  exact le_antisymm ((cdf μ).mono.leftLim_le le_rfl) (sub_nonpos.mp hz)

theorem continuous_atomless_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [atomless_cdf_leftLim μ x, (cdf μ).rightLim_eq x]

theorem exists_atomless_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ x : ℝ, cdf μ x = q := by
  have hi := isPreconnected_univ.intermediate_value_Ioo
    (f := cdf μ) (l₁ := atBot) (l₂ := atTop) (by simp) (by simp)
    (continuous_atomless_cdf μ).continuousOn (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ)
  obtain ⟨x, _, hx⟩ := hi ⟨hq0, hq1⟩
  exact ⟨x, hx⟩

theorem atomless_measure_Ioo_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (a b : ℝ) :
    μ (Ioo a b) = ENNReal.ofReal (cdf μ b - cdf μ a) := by
  simpa only [measure_cdf, atomless_cdf_leftLim] using (cdf μ).measure_Ioo (a := a) (b := b)

theorem exists_eight_ordered_quantiles (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∃ q : Fin 8 → ℝ, StrictMono q ∧ ∀ i, cdf μ (q i) = ((i.val : ℝ) + 1) / 9 := by
  choose q hq using fun i : Fin 8 => exists_atomless_quantile μ
    (q := ((i.val : ℝ) + 1) / 9) (by positivity) (by
      have hi : (i.val : ℝ) < 8 := by exact_mod_cast i.isLt
      apply (div_lt_one (by norm_num : (0 : ℝ) < 9)).mpr
      linarith)
  refine ⟨q, ?_, hq⟩
  intro i j hij
  by_contra hn
  have hle := (cdf μ).mono (le_of_not_gt hn)
  rw [hq i, hq j] at hle
  have hval : (i.val : ℝ) < j.val := by exact_mod_cast hij
  linarith

end CircleDomainRigidity

end

end OAI
