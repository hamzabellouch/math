import OAI.NumberTheory.CubicMoment.Estimates.GaussianSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

/-! Holomorphic polynomial Gaussians and the anti-holomorphic raising
operator used for the fixed angular Fourier transform. -/
noncomputable section
open scoped SchwartzMap
open LineDeriv
namespace CubicFirstMoment

def harmonicGaussian (a : ℝ) (ha : 0 < a) (n : ℕ) : 𝓢(ℂ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => z^n) (radialGaussianSchwartz a ha)

@[simp] lemma harmonicGaussian_apply (a : ℝ) (ha : 0 < a) (n : ℕ) (z : ℂ) :
    harmonicGaussian a ha n z = z^n*(radialGaussian a z:ℂ) := by
  rw [harmonicGaussian,SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  rfl

lemma gaussianComplex_fderiv (a : ℝ) (ha : 0 < a) (z v : ℂ) :
    fderiv ℝ (radialGaussianSchwartz a ha) z v =
      ((-2*a*inner ℝ z v*radialGaussian a z:ℝ):ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((radialGaussian_smooth a).differentiable (by simp) |>.differentiableAt.hasFDerivAt)
  have he : (radialGaussianSchwartz a ha : ℂ → ℂ) = Complex.ofRealCLM ∘ radialGaussian a := rfl
  rw [he,h.fderiv,radialGaussian_fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    gaussianLogDerivative,smul_eq_mul,Complex.ofRealCLM_apply]
  congr 1
  change radialGaussian a z*((-2*a)*inner ℝ z v) = -2*a*inner ℝ z v*radialGaussian a z
  ring

lemma harmonicGaussian_fderiv (a : ℝ) (ha : 0 < a) (n : ℕ) (z v : ℂ) :
    fderiv ℝ (harmonicGaussian a ha n) z v =
      (n:ℂ)*z^(n-1)*v*(radialGaussian a z:ℂ) +
        z^n*((-2*a*inner ℝ z v*radialGaussian a z:ℝ):ℂ) := by
  have he : (harmonicGaussian a ha n : ℂ → ℂ) =
      (fun z : ℂ => z^n*radialGaussianSchwartz a ha z) := by
    ext z
    exact harmonicGaussian_apply a ha n z
  rw [he,fderiv_fun_mul (by fun_prop) (radialGaussianSchwartz a ha).differentiableAt]
  simp only [add_apply,smul_apply,
    smul_eq_mul, fderiv_pow_ring,ContinuousLinearMap.id_apply,nsmul_eq_mul,
    gaussianComplex_fderiv,radialGaussianSchwartz_apply,radialGaussian]
  ring

lemma harmonicGaussian_raising (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∂_{(1:ℂ)} (harmonicGaussian a ha n)) +
      Complex.I • (∂_{Complex.I} (harmonicGaussian a ha n)) =
        ((-2*a:ℝ):ℂ) • harmonicGaussian a ha (n+1) := by
  ext z
  simp only [add_apply,smul_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,harmonicGaussian_fderiv,
    harmonicGaussian_apply,smul_eq_mul]
  have hi1 : inner ℝ z (1:ℂ) = z.re := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  have hiI : inner ℝ z Complex.I = z.im := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  rw [hi1,hiI,pow_succ]
  push_cast
  have hz : (z.re:ℂ)+(z.im:ℂ)*Complex.I = z := Complex.re_add_im z
  calc
    _ = (-2*(a:ℂ))*z^n*((z.re:ℂ)+(z.im:ℂ)*Complex.I)*(radialGaussian a z:ℂ) := by
      ring_nf
      simp only [Complex.I_sq]
      ring
    _ = _ := by rw [hz]; ring

end CubicFirstMoment

end

end OAI
