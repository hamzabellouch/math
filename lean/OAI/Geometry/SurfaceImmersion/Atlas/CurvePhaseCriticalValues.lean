import OAI.Geometry.SurfaceImmersion.Atlas.CurvePhaseParameterGraph

namespace OAI

/-! Degenerate tangencies along a curve form a null set of linear phase
parameters. The first-coordinate chart of the critical equation suffices
where the first velocity component is nonzero. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
local instance curvePlaneVolumeHaar : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

lemma curvePhaseParameterGraph_differentiableAt {u v : ℝ → CurvePlane} {L : ℝ}
    {x : CurvePlane} (hu : DifferentiableAt ℝ u x.1) (hv : DifferentiableAt ℝ v x.1)
    (hspeed : (v x.1).1 ≠ 0) :
    DifferentiableAt ℝ (curvePhaseParameterGraph u v L) x := by
  have huc : DifferentiableAt ℝ (fun z : CurvePlane => u z.1) x :=
    hu.comp x differentiableAt_fst
  have hvc : DifferentiableAt ℝ (fun z : CurvePlane => v z.1) x :=
    hv.comp x differentiableAt_fst
  have hsnd : DifferentiableAt ℝ (Prod.snd : CurvePlane → ℝ) x := differentiableAt_snd
  have hnum : DifferentiableAt ℝ (fun z : CurvePlane =>
      -z.2*(v z.1).2-L*((u z.1).1*(v z.1).1+(u z.1).2*(v z.1).2)) x :=
    (hsnd.neg.mul hvc.snd).sub
    (((huc.fst.mul hvc.fst).add (huc.snd.mul hvc.snd)).const_mul L)
  have hquot := hnum.mul (hvc.fst.inv hspeed)
  convert hquot.prodMk hsnd using 1
  funext z
  simp only [curvePhaseParameterGraph,Pi.mul_apply,Pi.inv_apply,div_eq_mul_inv]

lemma curvePhaseParameterGraph_singular {u v w : ℝ → CurvePlane} {L t : ℝ}
    {ell : CurvePlane} (hu : HasDerivAt u (v t) t) (hv : HasDerivAt v (w t) t)
    (hspeed : (v t).1 ≠ 0)
    (hcrit : curvePhaseVelocity u v L t ell = 0)
    (hdeg : curvePhaseAcceleration u v w L t ell = 0) :
    ¬ Function.Surjective (fderiv ℝ (curvePhaseParameterGraph u v L) (t,ell.2)) := by
  have hdiff := curvePhaseParameterGraph_differentiableAt (L := L) (x := (t,ell.2))
    hu.differentiableAt hv.differentiableAt hspeed
  have hline : HasDerivAt (fun s : ℝ => (s,ell.2)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t ell.2)
  have hchain := hdiff.hasFDerivAt.comp_hasDerivAt t hline
  have hz := curvePhaseParameterGraph_deriv_zero hu hv hspeed hcrit hdeg
  have hval : fderiv ℝ (curvePhaseParameterGraph u v L) (t,ell.2) (1,0) = 0 :=
    hchain.unique hz
  intro hsurj
  have hinj : Function.Injective (fderiv ℝ (curvePhaseParameterGraph u v L) (t,ell.2)) :=
    LinearMap.injective_iff_surjective.mpr hsurj
  have he : (1,0) = (0 : CurvePlane) := hinj (hval.trans (map_zero _).symm)
  exact one_ne_zero (congrArg Prod.fst he)

/-- The bad parameter set is contained in the critical values of the explicit
two-dimensional parameter graph. -/
theorem curve_phase_degenerate_parameters_null
    (u v w : ℝ → CurvePlane) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hdu : ∀ t, HasDerivAt u (v t) t) (hdv : ∀ t, HasDerivAt v (w t) t) (L : ℝ) :
    volume {ell : CurvePlane | ∃ t, (v t).1 ≠ 0 ∧
      curvePhaseVelocity u v L t ell = 0 ∧ curvePhaseAcceleration u v w L t ell = 0} = 0 := by
  let f := curvePhaseParameterGraph u v L
  let S : Set CurvePlane := {z | (v z.1).1 ≠ 0 ∧ ¬ Function.Surjective (fderiv ℝ f z)}
  have hnull : volume (f '' S) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ f x)
    · intro x hx
      exact (curvePhaseParameterGraph_differentiableAt
        (hu.differentiable (by simp) x.1) (hv.differentiable (by simp) x.1) hx.1).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      change LinearMap.det (fderiv ℝ f x).toLinearMap = 0
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot,ne_eq,LinearMap.ker_eq_bot]
      exact fun hi => hx.2 (LinearMap.injective_iff_surjective.mp hi)
  apply measure_mono_null _ hnull
  rintro ell ⟨t,hspeed,hcrit,hdeg⟩
  exact ⟨(t,ell.2),⟨hspeed,curvePhaseParameterGraph_singular (hdu t) (hdv t)
    hspeed hcrit hdeg⟩,curvePhaseParameterGraph_eq hspeed hcrit⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
