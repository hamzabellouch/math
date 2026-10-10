import OAI.Geometry.EinsteinFour.MetricDistance
import Mathlib.MeasureTheory.Function.Jacobian

namespace OAI

/-! The noninjective change-of-variables inequality, with the target
volume density retained. This is the local coordinate inequality needed
for the exponential's image. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

theorem weighted_area_inequality {f : FourSpace → FourSpace}
    {D : FourSpace → FourSpace →L[ℝ] FourSpace} {s : Set FourSpace}
    (hs : MeasurableSet s) (hf : Measurable f)
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x)
    (W : FourSpace → ℝ≥0∞) (hW : Measurable W) :
    ∫⁻ y in f '' s, W y ≤
      ∫⁻ x in s, ENNReal.ofReal |(D x).det| * W (f x) := by
  let J := fun x => ENNReal.ofReal |(D x).det|
  have hJ : AEMeasurable J (volume.restrict s) :=
    aemeasurable_ofReal_abs_det_fderivWithin volume hs hd
  have hmeasure : volume.restrict (f '' s) ≤
      Measure.map f ((volume.restrict s).withDensity J) := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.restrict_apply hA, Measure.map_apply hf hA,
      withDensity_apply _ (hf hA), Measure.restrict_restrict (hf hA)]
    rw [← image_preimage_inter f s A]
    exact addHaar_image_le_lintegral_abs_det_fderiv volume ((hf hA).inter hs)
      (fun x hx => (hd x hx.2).mono inter_subset_right)
  have h := lintegral_mono' hmeasure (le_rfl : W ≤ W)
  have hcomp : AEMeasurable (fun x => W (f x)) (volume.restrict s) :=
    (hW.comp hf).aemeasurable
  rw [lintegral_map hW hf] at h
  rw [lintegral_withDensity_eq_lintegral_mul₀ hJ hcomp] at h
  exact h

end
end PositiveEinsteinFour.Geometry

end OAI
