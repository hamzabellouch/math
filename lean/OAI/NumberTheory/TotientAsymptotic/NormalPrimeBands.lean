import OAI.NumberTheory.TotientAsymptotic.NormalitySize
import OAI.NumberTheory.TotientAsymptotic.SmoothSuffix

namespace OAI

/-! Largest-factor bands derived from normality, including the small-prime case. -/

noncomputable section

namespace TotientAsymptotic

lemma largestPrimeFactor_le_self {n : ℕ} (hn : 1 ≤ n) : largestPrimeFactor n ≤ n := by
  apply largestPrimeFactor_le_of_prime_divisors hn
  intro p _ hp hn0
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp

lemma normality_total_uniform {S b : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSb : B S ≤ b) (hpb : B (p-1 : ℕ) ≤ b) :
    ((p-1).primeFactorsList.length : ℝ) ≤ 3*b := by
  by_cases hSn : S < (p-1 : ℕ)
  · exact (normality_total_bound hp hS hSn hBS).trans (by linarith)
  · have hpn : 1 ≤ p-1 := by have := hp.1.two_le; omega
    have hs : (largestPrimeFactor (p-1) : ℝ) ≤ S := by
      have hl : (largestPrimeFactor (p-1) : ℝ) ≤ (p-1 : ℕ) := by
        exact_mod_cast largestPrimeFactor_le_self hpn
      exact hl.trans (le_of_not_gt hSn)
    have hz := omegaIn_eq_zero_of_largest_le (T := (p-1 : ℕ)) hs
    have he := congrArg (fun n : ℕ => (n : ℝ)) (omegaIn_partition (p-1) S)
    rw [hz,Nat.add_zero] at he
    linarith [hp.2.1]

lemma shifted_doubleLog_lower {p : ℕ} (hp : 3 ≤ p) :
    B p-1 ≤ B (p-1 : ℕ) := by
  have hn : 2 ≤ p-1 := by omega
  have hnR : (1 : ℝ) < (p-1 : ℕ) := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpn : (p : ℝ) ≤ ((p-1 : ℕ) : ℝ)^2 := by
    have he : p-1+1=p := by omega
    have hs : p ≤ (p-1)^2 := by nlinarith
    exact_mod_cast hs
  have hl := Real.log_le_log hpR hpn
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hh := Real.log_le_log (Real.log_pos (show (1 : ℝ) < p by exact_mod_cast (show 1 < p by omega))) hl
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.log_pos hnR).ne'] at hh
  change Real.log (Real.log (p : ℝ))-1 ≤ Real.log (Real.log ((p-1 : ℕ) : ℝ))
  linarith [Real.log_two_lt_d9]

lemma normal_prime_largest_band {S b lo hi : ℝ} {p : ℕ}
    (hp : IsNormalPrime S p) (hp3 : 3 ≤ p) (hS : 1 < S)
    (hBS : 0 ≤ B S) (hSb : B S ≤ b) (hb : 0 < b)
    (hpb : B (p-1 : ℕ) ≤ b) (hlo : lo ≤ B p) (hhi : B p ≤ hi) :
    lo-1-Real.log (3*b) ≤ B (largestPrimeFactor (p-1)) ∧
      B (largestPrimeFactor (p-1)) ≤ hi := by
  have hn : 2 ≤ p-1 := by omega
  constructor
  · have hlow := largest_factor_doubleLog_lower hn (by positivity : 0 < 3*b)
      (normality_total_uniform hp hS hBS hSb hpb)
    linarith [shifted_doubleLog_lower hp3]
  · apply le_trans _ hhi
    have hl : (1 : ℝ) < largestPrimeFactor (p-1) := by
      exact_mod_cast one_lt_largestPrimeFactor hn
    apply Real.log_le_log (Real.log_pos hl)
    apply Real.log_le_log (zero_lt_one.trans hl)
    exact_mod_cast (largestPrimeFactor_le_self (by omega : 1 ≤ p-1)).trans (Nat.sub_le _ _)

end TotientAsymptotic

end

end OAI
