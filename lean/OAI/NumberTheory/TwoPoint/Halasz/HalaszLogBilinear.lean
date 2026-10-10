import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogCoefficients

namespace OAI

/-! Transfer the logarithmic bilinear sum to its complete-system Taylor
polynomial with an explicit uniform error. -/
namespace TwoPointCorrelations

open Finset Complex

lemma halasz_log_taylor_phase_factor (k : ℕ) (t : ℝ) {z : ℝ} (hz : z≠0) (a b : ℕ) :
    Complex.exp (Complex.I*((t*(Real.log z+halaszLogTaylor k z ((a*b:ℕ):ℝ)):ℝ):ℂ))=
      Complex.exp (Complex.I*((t*Real.log z:ℝ):ℂ))*
        halaszVinogradovCharacter (fun j : Fin k => ((a^(j.val+1):ℕ):ℤ))
          (halaszScaledFrequency (halaszLogCoefficient t z)
            (fun j => ((b^(j.val+1):ℕ):ℤ))) := by
  rw [halasz_log_taylor_character k t hz,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem halasz_log_bilinear_taylor (k M₁ M₂ : ℕ) (t : ℝ) {z : ℝ}
    (hz : 0<z) (hM : ((M₁*M₂:ℕ):ℝ)≤z/2) :
    ‖∑ b : Fin M₂,∑ a : Fin M₁,
      Complex.exp (Complex.I*((t*Real.log (z+(a.val+1)*(b.val+1)):ℝ):ℂ))‖≤
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖+
        ((M₁*M₂:ℕ):ℝ)*(2*|t| * (((M₁*M₂:ℕ):ℝ)/z)^(k+1)) := by
  let U := ∑ b : Fin M₂,∑ a : Fin M₁,
    Complex.exp (Complex.I*((t*Real.log (z+(a.val+1)*(b.val+1)):ℝ):ℂ))
  let V := ∑ b : Fin M₂,∑ a : Fin M₁,
    Complex.exp (Complex.I*((t*(Real.log z+
      halaszLogTaylor k z (((a.val+1)*(b.val+1):ℕ):ℝ)):ℝ):ℂ))
  have hdiff : ‖U-V‖≤((M₁*M₂:ℕ):ℝ)*(2*|t| * (((M₁*M₂:ℕ):ℝ)/z)^(k+1)) := by
    dsimp only [U,V]
    rw [← sum_sub_distrib]
    simp_rw [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum (fun _ _ => norm_sum_le _ _)).trans
    calc
      _ ≤ ∑ _b : Fin M₂,∑ _a : Fin M₁,
          (2*|t| * (((M₁*M₂:ℕ):ℝ)/z)^(k+1)) := by
        apply sum_le_sum
        intro b _
        apply sum_le_sum
        intro a _
        have hab : ((a.val+1)*(b.val+1):ℕ)≤M₁*M₂ :=
          Nat.mul_le_mul (by omega) (by omega)
        have habR : (((a.val+1)*(b.val+1):ℕ):ℝ)≤((M₁*M₂:ℕ):ℝ) := by exact_mod_cast hab
        have hh := halasz_log_taylor_phase k t hz
          (Nat.cast_nonneg ((a.val+1)*(b.val+1))) (habR.trans hM)
        have hp := pow_le_pow_left₀ (by positivity :
            0≤(((a.val+1)*(b.val+1):ℕ):ℝ)/z)
          (div_le_div_of_nonneg_right habR hz.le) (k+1)
        have hb := mul_le_mul_of_nonneg_left hp (by positivity : 0≤2*|t|)
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hh.trans hb
      _ = _ := by simp; ring
  have hV : ‖V‖=‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖ := by
    have he : V=Complex.exp (Complex.I*((t*Real.log z:ℝ):ℂ))*
        (∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
          (halaszScaledFrequency (halaszLogCoefficient t z)
            (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))) := by
      dsimp only [V]
      simp_rw [halasz_log_taylor_phase_factor k t hz.ne']
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      rw [halaszVinogradovPolynomial,mul_sum]
    rw [he,norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul]
  have hn : ‖U‖≤‖V‖+‖U-V‖ := by
    calc
      _ = ‖V+(U-V)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  exact hn.trans (by rw [hV]; exact add_le_add le_rfl hdiff)

end TwoPointCorrelations

end OAI
