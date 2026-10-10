import OAI.NumberTheory.JointDickman.Arithmetic.RationalPrimeHyperbola

namespace OAI

/-! # The rational hyperbola budget at the required logarithmic scales -/
namespace JointDickman

lemma rational_hyperbola_polylog_budget (N B : ℝ) (q : ℕ)
    (hN : 0 < N) (hB : 2 ≤ B) (hq : 0 < q)
    (hlog : Real.log N ≤ 3*B) (hqlo : B^12 ≤ q) (hqhi : (q:ℝ) ≤ N/B^8) :
    rationalHyperbolaBudget N (B^20) (Real.log (2*N)) q ≤ 64/B^6 := by
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hpow8 : 1 ≤ B^8 := one_le_pow₀ hB1
  have hqN : (q:ℝ) ≤ N := hqhi.trans (div_le_self hN.le hpow8)
  have hlq : Real.log q ≤ 3*B := (Real.log_le_log hq0 hqN).trans hlog
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hL : Real.log (2*N) ≤ 4*B := by
    rw [Real.log_mul (by norm_num) hN.ne']
    linarith
  have hL0 : 0 ≤ Real.log (2*N) := by
    have hN1 : 1 ≤ N := by
      have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
      exact hq1.trans hqN
    apply Real.log_nonneg
    linarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hpower (k : ℕ) (hk : 6 ≤ k) (c : ℝ) (hc : 0 ≤ c) : c/B^k ≤ c/B^6 := by
    apply div_le_div_of_nonneg_left hc (pow_pos hB0 6)
    exact pow_le_pow_right₀ hB1 hk
  have h1 : 2*Real.log (2*N)/B^20 ≤ 8/B^6 := by
    calc
      _ ≤ 2*(4*B)/B^20 := by gcongr
      _ = 8/B^19 := by field_simp; ring
      _ ≤ _ := hpower 19 (by norm_num) 8 (by norm_num)
  have h2 : 4*(1+Real.log q)/(q:ℝ) ≤ 16/B^6 := by
    calc
      _ ≤ 4*(1+3*B)/B^12 := by gcongr
      _ ≤ 16*B/B^12 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hB0.le 12)
        linarith
      _ = 16/B^11 := by field_simp
      _ ≤ _ := hpower 11 (by norm_num) 16 (by norm_num)
  have h3 : 4/B^20 ≤ 4/B^6 := hpower 20 (by norm_num) 4 (by norm_num)
  have h4 : 2*(q:ℝ)*(1+Real.log (2*N))/N ≤ 10/B^6 := by
    calc
      _ ≤ 2*(N/B^8)*(5*B)/N := by gcongr; linarith
      _ = 10/B^7 := by field_simp; ring
      _ ≤ _ := hpower 7 (by norm_num) 10 (by norm_num)
  unfold rationalHyperbolaBudget
  calc
    _ ≤ 8/B^6+16/B^6+4/B^6+10/B^6 := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = 38/B^6 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hB0.le 6)

end JointDickman

end OAI
