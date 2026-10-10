import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartGeometry
import OAI.Geometry.SurfaceImmersion.Geometry.CovectorPullbackParameters
import OAI.Geometry.SurfaceImmersion.Primitive.CircularBoundaryTangencies

namespace OAI

/-! A boundary transverse to a phase has a nonzero defining derivative in
that phase's second coordinate. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma phase_chart_transverse_definer_at {φ ρ : Base → ℝ} {f : Base → Base}
    {p : Base} (hφ : DifferentiableAt ℝ φ (f p)) (hρ : DifferentiableAt ℝ ρ (f p))
    (hf : DifferentiableAt ℝ f p) (hphase : φ ∘ f =ᶠ[𝓝 p] Prod.fst)
    (hD : coordDet (fderiv ℝ f p) ≠ 0)
    (hcross : covectorDet (phaseDerivative φ (f p)) (phaseDerivative ρ (f p)) ≠ 0) :
    fderiv ℝ (ρ ∘ f) p dy ≠ 0 := by
  have hcomp (ψ : Base → ℝ) (hψ : DifferentiableAt ℝ ψ (f p)) :
      phaseDerivative (ψ ∘ f) p = pullCovector (fderiv ℝ f p) (phaseDerivative ψ (f p)) := by
    unfold phaseDerivative
    rw [fderiv_comp p hψ hf]
    change ((fderiv ℝ ψ (f p)) ((fderiv ℝ f p) dx),
      (fderiv ℝ ψ (f p)) ((fderiv ℝ f p) dy)) = _
    conv_lhs => rw [← phaseLinear_phaseDerivative ψ (f p)]
    rfl
  have hfirst : pullCovector (fderiv ℝ f p) (phaseDerivative φ (f p)) = dx := by
    rw [← hcomp φ hφ]
    unfold phaseDerivative
    rw [hphase.fderiv_eq,fderiv_fst]
    rfl
  have hdet := covectorDet_pullback (fderiv ℝ f p)
    (phaseDerivative φ (f p)) (phaseDerivative ρ (f p))
  rw [hfirst,← hcomp ρ hρ] at hdet
  have hne := mul_ne_zero hD hcross
  rw [← hdet] at hne
  simpa only [covectorDet,dx,phaseDerivative,one_mul,zero_mul,sub_zero] using hne

lemma phase_chart_transverse_definer {φ ρ : Base → ℝ} {f : Base → Base}
    (hφ : ContDiff ℝ ∞ φ) (hρ : ContDiff ℝ ∞ ρ) (hf : ContDiff ℝ ∞ f)
    {p : Base} (hphase : φ ∘ f =ᶠ[𝓝 p] Prod.fst)
    (hD : coordDet (fderiv ℝ f p) ≠ 0)
    (hcross : covectorDet (phaseDerivative φ (f p)) (phaseDerivative ρ (f p)) ≠ 0) :
    fderiv ℝ (ρ ∘ f) p dy ≠ 0 := by
  have hfirst : pullCovector (fderiv ℝ f p) (phaseDerivative φ (f p)) = dx := by
    rw [← phaseDerivative_comp_smooth hφ hf]
    unfold phaseDerivative
    rw [hphase.fderiv_eq,fderiv_fst]
    rfl
  have hdet := covectorDet_pullback (fderiv ℝ f p)
    (phaseDerivative φ (f p)) (phaseDerivative ρ (f p))
  rw [hfirst,← phaseDerivative_comp_smooth hρ hf] at hdet
  have hne := mul_ne_zero hD hcross
  rw [← hdet] at hne
  simpa only [covectorDet,dx,phaseDerivative,one_mul,zero_mul,sub_zero] using hne

lemma circular_radius_phase_determinant (φ : Base → ℝ) (c p : Base) :
    covectorDet (phaseDerivative φ p) (phaseDerivative (circularRadiusSquared c) p) =
      -2 * phaseLinear (phaseDerivative φ p)
        (FiniteOrderSmoothing.circularAngularTangent c p) := by
  have hx := circularRadiusSquared_derivative c p dx
  have hy := circularRadiusSquared_derivative c p dy
  unfold covectorDet phaseDerivative
  change coordDeriv dx φ p * coordDeriv dy (circularRadiusSquared c) p -
    coordDeriv dy φ p * coordDeriv dx (circularRadiusSquared c) p = _
  rw [hx,hy]
  simp only [phaseLinear_apply,FiniteOrderSmoothing.circularAngularTangent,dx,dy]
  dsimp [coordDeriv]
  ring

lemma phase_chart_circular_definer {φ : Base → ℝ} {f : Base → Base}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    {p : Base} (hphase : φ ∘ f =ᶠ[𝓝 p] Prod.fst)
    (hD : coordDet (fderiv ℝ f p) ≠ 0) (c : Base) (r : ℝ)
    (hcross : phaseLinear (phaseDerivative φ (f p))
      (FiniteOrderSmoothing.circularAngularTangent c (f p)) ≠ 0) :
    fderiv ℝ (fun x => circularRadiusSquared c (f x) - r^2) p dy ≠ 0 := by
  have h := phase_chart_transverse_definer hφ (circularRadiusSquared_smooth c) hf
    hphase hD (by rw [circular_radius_phase_determinant]; exact mul_ne_zero (by norm_num) hcross)
  have he : (fun x => circularRadiusSquared c (f x) - r^2) =
      (circularRadiusSquared c ∘ f) - (fun _ => r^2) := rfl
  rw [he,fderiv_sub (((circularRadiusSquared_smooth c).comp hf).differentiable (by simp) p) (differentiableAt_const _)]
  simpa using h

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
