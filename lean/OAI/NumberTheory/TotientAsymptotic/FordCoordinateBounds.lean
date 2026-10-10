import OAI.NumberTheory.TotientAsymptotic.FordFactorization
import OAI.NumberTheory.TotientAsymptotic.TotientPreimageBound

namespace OAI

/-! Concrete bounds and nondegeneracy of the two coordinates in the bootstrap. -/
noncomputable section
namespace TotientAsymptotic

lemma first_two_a_bounds : 0 < a 1 ∧ a 1 ≤ 1/2 ∧ 0 < a 2 ∧ a 2 ≤ 1 := by
  have h1 : a 1=2*Real.log 2-1 := by norm_num [a]
  have h2 : a 2=3*Real.log 3-2*Real.log 2-1 := by norm_num [a]
  refine ⟨a_pos (by norm_num),?_,a_pos (by norm_num),?_⟩
  · rw [h1]
    linarith [Real.log_two_lt_d9]
  · rw [h2]
    linarith [Real.log_three_lt_d9,Real.log_two_gt_d9]

lemma prime_preimage_B_bound {x : ℝ} {n p : ℕ} (hx : 2 ≤ x)
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hφ : (n.totient:ℝ) ≤ x) :
    B p ≤ B x+2 := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hφ0 : (0:ℝ) ≤ n.totient := Nat.cast_nonneg _
  have hnR : (n:ℝ) ≤ 2*x^2 := by
    have hn2 : (n:ℝ) ≤ 2*(n.totient:ℝ)^2 := by exact_mod_cast totient_preimage_quadratic hn
    exact hn2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hφ0 hφ 2) (by norm_num))
  have hpR : (p:ℝ) ≤ 2*x^2 := (Nat.cast_le.mpr (Nat.le_of_dvd hn hpn)).trans hnR
  have hlog := Real.log_le_log (by linarith : (0:ℝ)<p) hpR
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero _ hx0.ne'),Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlog2 : Real.log (2:ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hthree : Real.log p ≤ 3*Real.log x := by linarith
  have hh := Real.log_le_log (Real.log_pos hp1) hthree
  rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hlx.ne'] at hh
  have hl3 : Real.log (3:ℝ) ≤ 2 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num at ht
    exact ht
  exact hh.trans (by dsimp [B]; linarith)

lemma ford_coordinate_upper {x : ℝ} {n : ℕ} (hx : 4 ≤ x)
    (hn : 0 < n) (hφ : (n.totient:ℝ) ≤ x) (i : ℕ) :
    fordPrimeCoordinate n i ≤ B x+2 := by
  have hBx : 0 ≤ B x := by
    have hh : B 4 ≤ B x := Real.log_le_log (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) hx)
    have h4 : 0 < B 4 := by
      unfold B
      apply Real.log_pos
      rw [Real.log_four_eq]
      linarith [Real.log_two_gt_d9]
    exact h4.le.trans hh
  by_cases hi : i < n.primeFactorsList.length
  · have hp := fordPrime_prime hi
    have hmem : fordPrime n i ∈ n.primeFactorsList := by
      rw [fordPrime_eq_get hi]
      exact List.mem_reverse.mp (List.getElem_mem _)
    have hb := prime_preimage_B_bound (by linarith) hn hp (Nat.dvd_of_mem_primeFactorsList hmem) hφ
    exact max_le (by linarith) hb
  · have he : fordPrime n i=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
      rfl
    simp only [fordPrimeCoordinate,primeDoubleLog,he,Nat.cast_one,Real.log_one,Real.log_zero,max_self]
    linarith

lemma two_coordinate_failure_second_lower {x ω : ℝ} {n : ℕ} (hx : 4 ≤ x)
    (hBx : 0 ≤ B x) (hω : 0 ≤ ω) (hn : 0 < n) (hφ : (n.totient:ℝ) ≤ x)
    (hbad : (1+ω)*B x < a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2) :
    B x/2-1 < fordPrimeCoordinate n 2 := by
  obtain ⟨ha1,ha1',ha2,ha2'⟩ := first_two_a_bounds
  have h1 := ford_coordinate_upper hx hn hφ 1
  have h10 : 0 ≤ fordPrimeCoordinate n 1 := le_max_left _ _
  have h20 : 0 ≤ fordPrimeCoordinate n 2 := le_max_left _ _
  have hc1 := mul_le_mul_of_nonneg_right ha1' h10
  have hc2 := mul_le_mul_of_nonneg_right ha2' h20
  have hprod : 0 ≤ ω*B x := mul_nonneg hω hBx
  nlinarith only [hbad,h1,hc1,hc2,hprod]

/-- A violating pair has a genuinely large third prime factor. This also
rules out padded coordinates before applying the two-band estimate. -/
lemma two_coordinate_failure_large_second {x ω : ℝ} {n : ℕ} (hx : 4 ≤ x)
    (hBx : 12 ≤ B x) (hω : 0 ≤ ω) (hn : 0 < n) (hφ : (n.totient:ℝ) ≤ x)
    (hbad : (1+ω)*B x < a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2) :
    4 < primeDoubleLog n 2 ∧ 3 ≤ n.primeFactorsList.length := by
  obtain ⟨ha1,ha1',ha2,ha2'⟩ := first_two_a_bounds
  have h1 := ford_coordinate_upper hx hn hφ 1
  have h10 : 0 ≤ fordPrimeCoordinate n 1 := le_max_left _ _
  have h20 : 0 ≤ fordPrimeCoordinate n 2 := le_max_left _ _
  have hc1 := mul_le_mul_of_nonneg_right ha1' h10
  have hc2 := mul_le_mul_of_nonneg_right ha2' h20
  have hprod : 0 ≤ ω*B x := mul_nonneg hω (by linarith)
  have hlarge : 4 < fordPrimeCoordinate n 2 := by
    nlinarith only [hbad,h1,hc1,hc2,hprod,hBx]
  have hraw : 4 < primeDoubleLog n 2 := by
    change 4 < max 0 (primeDoubleLog n 2) at hlarge
    exact (lt_max_iff.mp hlarge).resolve_left (by norm_num)
  have hindex := fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) hraw)
  exact ⟨hraw,by omega⟩

end TotientAsymptotic

end

end OAI
