import OAI.Geometry.EinsteinFour.CotangentJacobian
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace OAI

/-! The change-of-variables step for local cotangent maps. The determinant
condition is the conclusion of the variational calculation, not an
assumption of measure preservation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set

noncomputable section

/-- A locally injective map with unit absolute derivative determinant
preserves coordinate volume on its domain. -/
theorem cotangent_map_volume_of_det_one
    (f : CotangentCoordinates → CotangentCoordinates)
    (s : Set CotangentCoordinates) (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, |(cotangentJacobian f x).det| = 1) :
    Measure.map f (volume.restrict s) = volume.restrict (f '' s) := by
  let : IsAddHaarMeasure (volume : Measure CotangentCoordinates) :=
    inferInstanceAs (IsAddHaarMeasure
      ((volume : Measure FourSpace).prod (volume : Measure FourSpace)))
  have hd : ∀ x ∈ s, |(fderiv ℝ f x).det| = 1 := by
    intro x hx
    rw [← cotangentJacobian_det f x (hf x hx)]
    exact hdet x hx
  have hden : (volume.restrict s).withDensity
      (fun x => ENNReal.ofReal |(fderiv ℝ f x).det|) = volume.restrict s := by
    calc
      _ = (volume.restrict s).withDensity 1 := by
        apply withDensity_congr_ae
        filter_upwards [ae_restrict_mem hs] with x hx
        simp only [hd x hx, ENNReal.ofReal_one, Pi.one_apply]
      _ = _ := withDensity_one
  have h := map_withDensity_abs_det_fderiv_eq_addHaar volume hs.nullMeasurableSet
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) hinj
  rwa [hden] at h

end
end PositiveEinsteinFour.Geometry

end OAI
