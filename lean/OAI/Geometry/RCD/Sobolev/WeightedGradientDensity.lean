import OAI.Geometry.RCD.Sobolev.GradientEnergyFromDensity
import Mathlib.MeasureTheory.Measure.FiniteMeasure

namespace OAI

/-! # Compact weighted energy from the actual limiting density

The weight is supported where the sharp density comparison holds. Absolute
continuity is retained explicitly; it is supplied by energy-measure domination.
-/

open Set Filter MeasureTheory
open scoped ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem weighted_gradient_energy_from_density {n : ℕ}
    (ν : FiniteMeasure (Euclidean n)) (g : Euclidean n → ℝ)
    {A : Set (Euclidean n)} (hA : MeasurableSet A)
    (hν : (ν : Measure (Euclidean n)) ≪ volume)
    {V : ℝ} (φ : Euclidean n →ᵇ ℝ)
    (hφ : ∀ x, 0≤φ x) (hs : Function.support φ ⊆ A)
    (hb : ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict A,
      ‖fderiv ℝ g x‖^2≤V*((ν : Measure (Euclidean n)).rnDeriv volume x).toReal) :
    Integrable (fun x => φ x*‖fderiv ℝ g x‖^2) volume ∧
      (∫ x, φ x*‖fderiv ℝ g x‖^2)≤V*∫ x, φ x ∂(ν : Measure (Euclidean n)) := by
  have hi := ((integrable_toReal_rnDeriv_mul_iff hν).2
    (φ.integrable (ν : Measure (Euclidean n)))).const_mul V
  have hbound : ∀ᵐ x ∂(volume : Measure (Euclidean n)),
      φ x*‖fderiv ℝ g x‖^2≤
        V*(((ν : Measure (Euclidean n)).rnDeriv volume x).toReal*φ x) := by
    filter_upwards [(ae_restrict_iff' hA).mp hb] with x hx
    by_cases hm : x∈A
    · nlinarith [mul_le_mul_of_nonneg_left (hx hm) (hφ x)]
    · have hz : φ x=0 := Function.notMem_support.mp (fun h => hm (hs h))
      simp only [hz,zero_mul,mul_zero,le_refl]
  have hmeas : AEStronglyMeasurable (fun x => φ x*‖fderiv ℝ g x‖^2) volume :=
    (φ.continuous.measurable.mul ((measurable_fderiv ℝ g).norm.pow_const 2)).aestronglyMeasurable
  have hprod : Integrable (fun x => φ x*‖fderiv ℝ g x‖^2) volume := by
    apply hi.mono' hmeas
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hφ x) (sq_nonneg _))] using hx
  refine ⟨hprod, (integral_mono_ae hprod hi hbound).trans_eq ?_⟩
  rw [integral_const_mul,integral_toReal_rnDeriv_mul hν]

end RegularPointCoordinates

end

end OAI
