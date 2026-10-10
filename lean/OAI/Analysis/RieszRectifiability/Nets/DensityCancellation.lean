import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzL2Density

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

theorem bounded_div_density_memLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (c B : ℝ) (hc : 0 < c)
    (hlower : ∀ x, c ≤ f x) (hbound : ∀ x, |g x| ≤ B) :
    MemLp (fun x => g x / f x) 2 μ := by
  apply MemLp.of_bound (hg.div hf).aestronglyMeasurable (B / c)
  apply Eventually.of_forall
  intro x
  rw [Pi.div_apply, Real.norm_eq_abs, abs_div, abs_of_pos (hc.trans_le (hlower x))]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) hc (hlower x)).trans
    (div_le_div_of_nonneg_right (hbound x) hc.le)

theorem integral_mul_div_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x)
    (F g : α → ℝ) :
    (∫ x, F x * (g x / f x) ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, F x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [ENNReal.toReal_ofReal (hpos x).le, smul_eq_mul]
  field_simp [(hpos x).ne']

theorem setIntegral_mul_div_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x)
    (U : Set α) (hU : MeasurableSet U) (F g : α → ℝ) :
    (∫ x in U, F x * (g x / f x) ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x in U, F x * g x ∂μ := by
  rw [restrict_withDensity hU]
  exact integral_mul_div_density (μ.restrict U) f hf hpos F g

theorem positive_density_absolutelyContinuous {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x) :
    μ ≪ μ.withDensity (fun x => ENNReal.ofReal (f x)) :=
  withDensity_absolutelyContinuous' hf.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hpos x)).ne')

end

end RieszRectifiability

end OAI
