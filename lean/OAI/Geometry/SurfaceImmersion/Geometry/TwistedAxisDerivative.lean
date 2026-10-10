import OAI.Geometry.SurfaceImmersion.Geometry.TwistedTargetTube

namespace OAI

/-! The supported twist turns the transverse derivative while retaining
 the whole longitudinal axis and its derivative. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma twistedRuledCoordinates_axis_fderiv {θ : Base → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (t : ℝ) (v : Base) :
    fderiv ℝ (twistedRuledCoordinates θ) (crosscapAxis t) v =
      (![Real.cos (θ (crosscapAxis t))*v 0,Real.sin (θ (crosscapAxis t))*v 0],v 1) := by
  rw [(twistedRuledCoordinates_hasFDerivAt hθ _).fderiv,twistedRuledDerivative_apply]
  simp [crosscapAxis_apply]

lemma twistedTubeSurface_axis (T : Base × ℝ → Fin 3 → ℝ) (θ : Base → ℝ) (t : ℝ) :
    twistedTubeSurface T θ (crosscapAxis t) = twistedTubeSurface T 0 (crosscapAxis t) := by
  simp only [twistedTubeSurface,Function.comp_apply,twistedRuledCoordinates_axis]

lemma twistedTubeSurface_axis_fderiv {T : Base × ℝ → Fin 3 → ℝ} {θ : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hθ : ContDiff ℝ ∞ θ) (t : ℝ) (v : Base) :
    fderiv ℝ (twistedTubeSurface T θ) (crosscapAxis t) v =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        (fderiv ℝ T (0,t) (![Real.cos (θ (crosscapAxis t))*v 0,
          Real.sin (θ (crosscapAxis t))*v 0],v 1)) := by
  rw [twistedTubeSurface,fderiv_comp _ (EuclideanSpace.equiv (Fin 3) ℝ).symm.differentiableAt
    ((hT.comp (twistedRuledCoordinates_smooth hθ)).differentiable (by simp) _),
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.fderiv,
    fderiv_comp _ (hT.differentiable (by simp) _)
      ((twistedRuledCoordinates_smooth hθ).differentiable (by simp) _)]
  simp only [ContinuousLinearMap.comp_apply,twistedRuledCoordinates_axis,
    twistedRuledCoordinates_axis_fderiv hθ]
  rfl

lemma twistedTubeSurface_longitudinal {T : Base × ℝ → Fin 3 → ℝ} {θ : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hθ : ContDiff ℝ ∞ θ) (t : ℝ) :
    fderiv ℝ (twistedTubeSurface T θ) (crosscapAxis t) (![0,1] : Base) =
      fderiv ℝ (twistedTubeSurface T 0) (crosscapAxis t) (![0,1] : Base) := by
  rw [twistedTubeSurface_axis_fderiv hT hθ,twistedTubeSurface_axis_fderiv (θ := 0) hT contDiff_const]
  simp

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
