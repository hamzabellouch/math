import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogTaylor
import OAI.NumberTheory.TwoPoint.Halasz.HalaszScaledFrequency

namespace OAI

/-! Identification of the logarithmic Taylor polynomial with the exact
coefficient-torus character in the double mean-value estimate. -/
namespace TwoPointCorrelations

open Finset Complex

noncomputable def halaszLogCoefficient {k : ℕ} (t z : ℝ) (j : Fin k) : ℝ :=
  t*(-1:ℝ)^j.val/(2*Real.pi*(j.val+1)*z^(j.val+1))

lemma halasz_log_coefficient_ne_zero {k : ℕ} {t z : ℝ}
    (ht : t≠0) (hz : z≠0) (j : Fin k) : halaszLogCoefficient t z j≠0 := by
  unfold halaszLogCoefficient
  exact div_ne_zero (mul_ne_zero ht (pow_ne_zero _ (by norm_num)))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (by positivity)) (pow_ne_zero _ hz))

lemma halasz_log_coefficient_abs {k : ℕ} (t z : ℝ) (j : Fin k) :
    |halaszLogCoefficient t z j|=|t|/(2*Real.pi*(j.val+1)*|z|^(j.val+1)) := by
  simp only [halaszLogCoefficient,abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,
    mul_one,abs_of_nonneg (by norm_num : 0≤(2:ℝ)),abs_of_pos Real.pi_pos]
  rw [abs_of_nonneg (show 0≤(j.val:ℝ)+1 by positivity)]

lemma halasz_log_taylor_character (k : ℕ) (t : ℝ) {z : ℝ} (hz : z≠0) (a b : ℕ) :
    halaszVinogradovCharacter (fun j : Fin k => ((a^(j.val+1):ℕ):ℤ))
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => ((b^(j.val+1):ℕ):ℤ)))=
      Complex.exp (Complex.I*((t*halaszLogTaylor k z ((a*b:ℕ):ℝ):ℝ):ℂ)) := by
  have he (j : Fin k) :
      fourier ((a^(j.val+1):ℕ):ℤ)
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => ((b^(j.val+1):ℕ):ℤ)) j)=
      Complex.exp (Complex.I*((t*((-1:ℝ)^j.val*
        (((a*b:ℕ):ℝ)/z)^(j.val+1)/(j.val+1)):ℝ):ℂ)) := by
    dsimp only [halaszScaledFrequency]
    rw [fourier_coe_apply]
    dsimp only [halaszLogCoefficient]
    congr 1
    push_cast
    have hzC : (z:ℂ)≠0 := by exact_mod_cast hz
    have hpiC : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
    simp only [div_pow,mul_pow]
    field_simp [hzC,hpiC]
  unfold halaszVinogradovCharacter
  simp_rw [he]
  rw [← Complex.exp_sum]
  congr 1
  rw [halaszLogTaylor,← Fin.sum_univ_eq_sum_range]
  push_cast
  rw [mul_sum,mul_sum]

end TwoPointCorrelations

end OAI
