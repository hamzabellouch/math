import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicPrimeInput

namespace OAI

/-! The elementary logarithmic exponent bookkeeping for the rescaled
prime estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma log_length_comparison {L Y c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (hlog : 1 ≤ Real.log L) (hY : L^c ≤ Y) :
    0 < Real.log Y ∧ 1+Real.log L ≤ (2/c)*Real.log Y := by
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hL c) hY
  rw [Real.log_rpow hL] at hl
  have hpos : 0 < Real.log Y := (mul_pos hc (by linarith)).trans_le hl
  refine ⟨hpos,?_⟩
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  nlinarith

lemma log_variation_power {z R M B u : ℝ} (hz : 1 ≤ z) (hR : 1 ≤ R)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (m b U : ℕ) (hu : |u| ≤ z^U) :
    2*M*z^m+(R-1)*(B*z^b+M*z^m*|u|) ≤
      (2*M+(R-1)*(B+M))*z^(m+b+U) := by
  have hm : z^m ≤ z^(m+b+U) := pow_le_pow_right₀ hz (by omega)
  have hb : z^b ≤ z^(m+b+U) := pow_le_pow_right₀ hz (by omega)
  have hmu : z^m*|u| ≤ z^(m+b+U) := by
    calc
      _ ≤ z^m*z^U := mul_le_mul_of_nonneg_left hu (pow_nonneg (by linarith) _)
      _ = z^(m+U) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hz (by omega)
  have h₁ := mul_le_mul_of_nonneg_left hm (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hM)
  have h₂ := mul_le_mul_of_nonneg_left hb hB
  have h₃ := mul_le_mul_of_nonneg_left hmu hM
  have h₄ := mul_le_mul_of_nonneg_left (add_le_add h₂ h₃) (sub_nonneg.mpr hR)
  nlinarith

lemma log_power_quotient {z a d : ℝ} (hz : 0 < z) (ha : 0 < a)
    (hza : z ≤ d*a) (n k : ℕ) : z^n/a^(n+k) ≤ d^(n+k)/z^k := by
  apply (div_le_div_iff₀ (pow_pos ha _) (pow_pos hz _)).mpr
  rw [← pow_add,← mul_pow]
  exact pow_le_pow_left₀ hz.le hza _

end CubicFirstMoment

end

end OAI
