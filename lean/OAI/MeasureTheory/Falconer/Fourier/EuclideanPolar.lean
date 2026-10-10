import OAI.MeasureTheory.Falconer.Angular.SphereModel
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! Polar integration with the same sphere measure used in the radial input. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem euclidean_polar_lintegral {n : ℕ} (f : Space (n+1) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ w : Sphere (n+1), (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r^n) * f (r • (w : Space (n+1)))) ∂sphereMeasure (n+1)) = ∫⁻ x, f x := by
  have he := MeasurePreserving.symm (homeomorphUnitSphereProd (Space (n+1))).toMeasurableEquiv
    (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (Space (n+1))))
  have h := he.lintegral_comp
      (hf.comp measurable_subtype_coe)
  simp only [Function.comp_def] at h
  rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
    restrict_compl_singleton] at h
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.add_sub_cancel] at h
  rw [lintegral_prod _ (by fun_prop)] at h
  convert h using 1
  apply lintegral_congr
  intro w
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  exact (lintegral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => ENNReal.ofReal (r^n) * f (r • (w : Space (n+1))))).symm

theorem translated_euclidean_polar_lintegral {n : ℕ} (f : Space (n+1) → ℝ≥0∞)
    (hf : Measurable f) (x : Space (n+1)) :
    (∫⁻ w : Sphere (n+1), (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r^n) * f (x+r • (w : Space (n+1)))) ∂sphereMeasure (n+1)) = ∫⁻ y, f y := by
  exact (euclidean_polar_lintegral (fun y => f (x+y)) (by fun_prop)).trans
    (lintegral_add_left_eq_self (μ := (volume : Measure (Space (n+1)))) f x)

end Falconer

end OAI
