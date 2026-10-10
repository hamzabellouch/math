import OAI.NumberTheory.CubicMoment.Estimates.IdealLogDerivative

namespace OAI

/-! The nonnegative 3-4-1 combination for the actual ideal logarithmic
derivatives. This is the Euler-coefficient positivity used in the zero-free
argument, including the primes where a character vanishes. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma complex_341_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3+4*z.re+(z^2).re := by
  have hn : z.re^2+z.im^2 ≤ 1 := by
    calc
      _ = ‖z‖^2 := by rw [←Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply,pow_two]
      _ ≤ 1 := by nlinarith [_root_.norm_nonneg z]
  simp only [pow_two,Complex.mul_re]
  nlinarith [sq_nonneg (z.re+1)]

lemma idealMangoldt_term_re (χ : EisensteinIdealExponent → ℂ)
    (σ : ℝ) (ν : EisensteinIdealExponent) :
    ((((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)*
      (idealExponentNorm ν:ℂ)^(-(σ:ℂ))).re =
      (MvPowerSeries.coeff ν idealVonMangoldt:ℝ)*(χ ν).re*idealExponentNorm ν^(-σ) := by
  rw [←Complex.ofReal_neg,←Complex.ofReal_cpow (idealExponentNorm_pos ν).le]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_mul]

lemma idealMangoldt_real_hasSum (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun ν => (MvPowerSeries.coeff ν idealVonMangoldt:ℝ)*(χ ν).re*
      idealExponentNorm ν^(-σ))
      (normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)
        idealExponentNorm (σ:ℂ)).re := by
  have hs := (idealVonMangoldtDirichlet_norm_summable χ hχ
    (s := (σ:ℂ)) (by simpa using hσ)).of_norm
  simpa only [normDirichletSeries,idealMangoldt_term_re] using! Complex.hasSum_re hs.hasSum

theorem idealMangoldt_341_nonneg (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ 3*(normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ))
          idealExponentNorm (σ:ℂ)).re+
      4*(normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)
          idealExponentNorm (σ:ℂ)).re+
      (normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*(χ ν)^2)
          idealExponentNorm (σ:ℂ)).re := by
  have hsq : ∀ ν, ‖(χ ν)^2‖ ≤ 1 := by
    intro ν
    rw [norm_pow]
    nlinarith [hχ ν,_root_.norm_nonneg (χ ν)]
  have h0 := idealMangoldt_real_hasSum (fun _ => 1) (by simp) hσ
  have h1 := idealMangoldt_real_hasSum χ hχ hσ
  have h2 := idealMangoldt_real_hasSum (fun ν => (χ ν)^2) hsq hσ
  have h := ((h0.mul_left 3).add (h1.mul_left 4)).add h2
  simp only [mul_one,Complex.one_re] at h
  rw [←h.tsum_eq]
  apply tsum_nonneg
  intro ν
  have hp := mul_nonneg (idealVonMangoldt_coeff_nonneg ν)
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le (-σ))
  have hz := complex_341_nonneg (hχ ν)
  nlinarith [mul_nonneg hp hz]

theorem idealLogDeriv_341_nonneg (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ 3*(-logDeriv (normDirichletSeries (fun _ => 1) idealExponentNorm) (σ:ℂ)).re+
      4*(-logDeriv (normDirichletSeries χ idealExponentNorm) (σ:ℂ)).re+
      (-logDeriv (normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm) (σ:ℂ)).re := by
  have hsq : ∀ ν, ‖(χ ν)^2‖ ≤ 1 := by
    intro ν
    rw [norm_pow]
    nlinarith [hχ ν,_root_.norm_nonneg (χ ν)]
  rw [idealDirichlet_neg_logDeriv _ (by simp) (by simp) (by simp) (by simpa using hσ),
    idealDirichlet_neg_logDeriv χ hχ hχ0 hχadd (by simpa using hσ),
    idealDirichlet_neg_logDeriv _ hsq (by simp [hχ0])
      (by intro ν κ; rw [hχadd,mul_pow]) (by simpa using hσ)]
  simpa only [mul_one] using idealMangoldt_341_nonneg χ hχ hσ

end CubicFirstMoment

end

end OAI
