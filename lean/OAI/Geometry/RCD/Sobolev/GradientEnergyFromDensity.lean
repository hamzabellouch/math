import OAI.Geometry.RCD.Sobolev.EuclideanEnergyDifferentiation
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! # Integrating the sharp pointwise energy-density comparison -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem gradient_energy_from_density {n : ℕ} (ν : FiniteMeasure (Euclidean n))
    (g : Euclidean n → ℝ) (A : Set (Euclidean n)) {V : ℝ} (hV : 0≤V)
    (hb : ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict A,
      ‖fderiv ℝ g x‖^2≤V*((ν : Measure (Euclidean n)).rnDeriv volume x).toReal) :
    IntegrableOn (fun x => ‖fderiv ℝ g x‖^2) A volume ∧
      (∫ x in A, ‖fderiv ℝ g x‖^2)≤V*(ν : Measure (Euclidean n)).real A := by
  have hi := Measure.integrableOn_toReal_rnDeriv (μ := (ν : Measure (Euclidean n)))
    (ν := (volume : Measure (Euclidean n))) (s := A) (measure_ne_top _ _)
  have hupper := hi.const_mul V
  have hgrad : IntegrableOn (fun x => ‖fderiv ℝ g x‖^2) A volume := by
    apply hupper.mono' ((measurable_fderiv ℝ g).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖fderiv ℝ g x‖)] using hx
  refine ⟨hgrad,?_⟩
  calc
    (∫ x in A, ‖fderiv ℝ g x‖^2) ≤
        ∫ x in A, V*((ν : Measure (Euclidean n)).rnDeriv volume x).toReal :=
      integral_mono_ae hgrad hupper hb
    _ = V*(∫ x in A, ((ν : Measure (Euclidean n)).rnDeriv volume x).toReal) :=
      integral_const_mul _ _
    _ ≤ V*(ν : Measure (Euclidean n)).real A := mul_le_mul_of_nonneg_left
      (Measure.setIntegral_toReal_rnDeriv_le (measure_ne_top _ _)) hV

end RegularPointCoordinates

end

end OAI
