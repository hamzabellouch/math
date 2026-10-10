import OAI.Analysis.CircleDomains.Sobolev.SmoothDiskGreen

namespace OAI

/-! The smooth Jacobian boundary integral is the signed area of the
actual image curve, expressed using its real and imaginary coordinates. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def signedCurveArea (γ : ℝ → ℂ) : ℝ :=
    ∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im

 theorem complex_real_linear_decomposition (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = L 1 * z.re + L Complex.I * z.im := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

 theorem signedCurveArea_smooth_image {F : ℂ → ℂ} {γ : ℝ → ℂ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) :
    signedCurveArea (F ∘ γ) =
      planarFormIntegral (fun z => (F z).re * fderiv ℝ (fun w => (F w).im) z 1)
        (fun z => (F z).re * fderiv ℝ (fun w => (F w).im) z Complex.I) γ := by
  unfold signedCurveArea planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [Function.comp_def]
  have hf := (hF.differentiable (by simp)).differentiableAt (x := γ t)
  have hg := (hγ.differentiable (by simp)).differentiableAt (x := t)
  have hd := hf.hasFDerivAt.comp_hasDerivAt t hg.hasDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp (γ t) hf.hasFDerivAt
  have hie (v : ℂ) : fderiv ℝ (fun w => (F w).im) (γ t) v =
      (fderiv ℝ F (γ t) v).im := by
    change fderiv ℝ (Complex.imCLM ∘ F) (γ t) v = _
    rw [hi.fderiv]
    rfl
  have hde : deriv (fun x => F (γ x)) t = fderiv ℝ F (γ t) (deriv γ t) := by
    simpa only [Function.comp_def] using hd.deriv
  rw [hde]
  rw [← hie]
  rw [complex_real_linear_decomposition]
  ring

 theorem signedCurveArea_congr {γ η : ℝ → ℂ} (heq : γ = η) :
    signedCurveArea γ = signedCurveArea η := by rw [heq]

end CircleDomainRigidity

end

end OAI
