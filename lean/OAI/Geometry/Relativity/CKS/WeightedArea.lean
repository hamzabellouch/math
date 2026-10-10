import OAI.Geometry.Relativity.CKS.SurfaceVolume

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CKSSurfaceVolume
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma restrict_image_le_map_jacobian {s : Set E} (hs : MeasurableSet s)
    {f : E → E} (hm : Measurable f) {f' : E → E →L[ℝ] E}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    volume.restrict (f '' s) ≤
      Measure.map f ((volume.restrict s).withDensity (fun x => ENNReal.ofReal |(f' x).det|)) := by
  apply Measure.le_iff.mpr
  intro t ht
  rw [Measure.restrict_apply ht, Measure.map_apply hm ht, withDensity_apply _ (ht.preimage hm),
    Measure.restrict_restrict (ht.preimage hm)]
  rw [← image_preimage_inter]
  exact addHaar_image_le_lintegral_abs_det_fderiv volume ((ht.preimage hm).inter hs)
    (fun x hx => (hd x hx.2).mono inter_subset_right)

lemma lintegral_image_le_jacobian {s : Set E} (hs : MeasurableSet s)
    {f : E → E} (hm : Measurable f) {f' : E → E →L[ℝ] E}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (w : E → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ y in f '' s, w y ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * w (f x) := by
  calc
    _ ≤ ∫⁻ y, w y ∂Measure.map f
        ((volume.restrict s).withDensity (fun x => ENNReal.ofReal |(f' x).det|)) :=
      lintegral_mono' (restrict_image_le_map_jacobian hs hm hd) le_rfl
    _ = ∫⁻ x, w (f x) ∂(volume.restrict s).withDensity
        (fun x => ENNReal.ofReal |(f' x).det|) := lintegral_map hw hm
    _ = _ := lintegral_withDensity_eq_lintegral_mul₀
      (aemeasurable_ofReal_abs_det_fderivWithin volume hs hd) (hw.comp hm).aemeasurable

lemma lintegral_image_le_jacobian_on {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hd : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (w : E → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ y in f '' s, w y ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * w (f x) := by
  classical
  let F := s.piecewise f (fun _ => 0)
  have hcont : ContinuousOn f s := fun x hx => (hd x hx).continuousWithinAt
  have hm : Measurable F := hcont.measurable_piecewise continuous_const.continuousOn hs
  have heq : EqOn F f s := piecewise_eqOn _ _ _
  have hdiff : ∀ x ∈ s, HasFDerivWithinAt F (f' x) s x := fun x hx =>
    (hd x hx).congr (fun z hz => heq hz) (heq hx)
  have h := lintegral_image_le_jacobian hs hm hdiff w hw
  have him : F '' s = f '' s := image_congr heq
  rw [him] at h
  refine h.trans_eq ?_
  apply setLIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [heq hx]

end CKSSurfaceVolume

end

end OAI
