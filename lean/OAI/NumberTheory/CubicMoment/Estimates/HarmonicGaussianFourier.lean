import OAI.NumberTheory.CubicMoment.Estimates.HarmonicGaussian

namespace OAI

/-! Exact Fourier transform of every holomorphic polynomial Gaussian. -/
noncomputable section
open scoped SchwartzMap FourierTransform
open LineDeriv FourierTransform
namespace CubicFirstMoment

lemma harmonicGaussian_fourier_step (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) :
    𝓕 (harmonicGaussian a ha (n+1)) w =
      (-(Real.pi:ℂ)*Complex.I/(a:ℂ))*w*𝓕 (harmonicGaussian a ha n) w := by
  have ht (m : ℂ) : (fun x : ℂ => inner ℝ x m).HasTemperateGrowth := by fun_prop
  have h := congrArg (fun f : 𝓢(ℂ,ℂ) => 𝓕 f w) (harmonicGaussian_raising a ha n)
  simp only [FourierTransform.fourier_add,FourierTransform.fourier_smul,SchwartzMap.fourier_lineDerivOp_eq,
    add_apply,smul_apply,SchwartzMap.smulLeftCLM_apply_apply
      (ht 1),
    SchwartzMap.smulLeftCLM_apply_apply
      (ht Complex.I),smul_eq_mul] at h
  have hi1 : inner ℝ w (1:ℂ) = w.re := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  have hiI : inner ℝ w Complex.I = w.im := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  rw [hi1,hiI] at h
  simp only [Complex.real_smul] at h
  have hw : (w.re:ℂ)+(w.im:ℂ)*Complex.I = w := Complex.re_add_im w
  have he : (2*(Real.pi:ℂ)*Complex.I)*w*𝓕 (harmonicGaussian a ha n) w =
      ((-2*a:ℝ):ℂ)*𝓕 (harmonicGaussian a ha (n+1)) w := by
    calc
      _ = (2*(Real.pi:ℂ)*Complex.I)*((w.re:ℂ)+(w.im:ℂ)*Complex.I)*
          𝓕 (harmonicGaussian a ha n) w := by rw [hw]
      _ = _ := by convert h using 1; ring
  have haC : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  apply (mul_left_cancel₀ (show (-2:ℂ)*(a:ℂ) ≠ 0 by exact mul_ne_zero (by norm_num) haC))
  push_cast at he
  calc
    _ = (2*(Real.pi:ℂ)*Complex.I)*w*𝓕 (harmonicGaussian a ha n) w := he.symm
    _ = _ := by field_simp

lemma harmonicGaussian_fourier (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) :
    𝓕 (harmonicGaussian a ha n) w =
      (-(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*w^n*
        𝓕 (radialGaussianSchwartz a ha) w := by
  induction n with
  | zero =>
      have he : harmonicGaussian a ha 0 = radialGaussianSchwartz a ha := by
        ext z
        rw [harmonicGaussian_apply,pow_zero,one_mul]
        rfl
      simp only [he,pow_zero,one_mul]
  | succ n ih =>
      rw [harmonicGaussian_fourier_step,ih,pow_succ,pow_succ]
      ring

lemma harmonicGaussian_traceFourier (a : ℝ) (ha : 0 < a) (n : ℕ) (w : ℂ) :
    traceFourier (harmonicGaussian a ha n) w =
      (-2*(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*(star w)^n*
        (Real.pi/a:ℝ)*(Real.exp (-4*Real.pi^2/a*Complex.normSq w):ℝ) := by
  rw [traceFourier_eq_fourier,←SchwartzMap.fourier_coe,harmonicGaussian_fourier]
  have hg := radialGaussianSchwartz_traceFourier a ha w
  rw [traceFourier_eq_fourier,←SchwartzMap.fourier_coe] at hg
  rw [hg,mul_pow]
  have he : (-(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*(2:ℂ)^n =
      (-2*(Real.pi:ℂ)*Complex.I/(a:ℂ))^n := by
    rw [←mul_pow]
    congr 1
    ring
  calc
    _ = ((-(Real.pi:ℂ)*Complex.I/(a:ℂ))^n*(2:ℂ)^n)*(star w)^n*
      ((Real.pi/a:ℝ)*(Real.exp (-4*Real.pi^2/a*Complex.normSq w):ℝ)) := by ring
    _ = _ := by rw [he]; ring

end CubicFirstMoment

end

end OAI
