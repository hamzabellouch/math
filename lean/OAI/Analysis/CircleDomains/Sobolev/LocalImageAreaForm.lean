import OAI.Analysis.CircleDomains.Sobolev.LocalComplexJacobianForm
import OAI.Analysis.CircleDomains.Sobolev.SmoothImageArea

namespace OAI

/-! The boundary-area identity requires smoothness only along the
actual parametrized curve. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma signedCurveArea_local_image {F : ℂ → ℂ} {γ : ℝ → ℂ}
    (hF : ∀ t, DifferentiableAt ℝ F (γ t)) (hγ : Differentiable ℝ γ) :
    signedCurveArea (F ∘ γ) =
      planarFormIntegral (fun z => (F z).re * fderiv ℝ (fun w => (F w).im) z 1)
        (fun z => (F z).re * fderiv ℝ (fun w => (F w).im) z Complex.I) γ := by
  unfold signedCurveArea planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [Function.comp_def]
  have hd := (hF t).hasFDerivAt.comp_hasDerivAt t (hγ t).hasDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp (γ t) (hF t).hasFDerivAt
  have hie (v : ℂ) : fderiv ℝ (fun w => (F w).im) (γ t) v =
      (fderiv ℝ F (γ t) v).im := by
    change fderiv ℝ (Complex.imCLM ∘ F) (γ t) v = _
    rw [hi.fderiv]
    rfl
  have hde : deriv (fun x => F (γ x)) t = fderiv ℝ F (γ t) (deriv γ t) := by
    simpa only [Function.comp_def] using hd.deriv
  rw [hde, ← hie, complex_real_linear_decomposition]
  ring

end CircleDomainRigidity

end

end OAI
