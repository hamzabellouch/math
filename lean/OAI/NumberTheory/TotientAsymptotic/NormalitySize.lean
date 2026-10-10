import OAI.NumberTheory.TotientAsymptotic.NormalityAlignment

namespace OAI

/-! Total factor counts and largest-factor locations for normal shifts. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

private lemma interval_count_partition (l : List ℕ) (n : ℕ) (S : ℝ)
    (hl : ∀ p ∈ l, 1 < p ∧ p ≤ n) :
    (l.filter (fun p : ℕ => decide ((1 : ℝ) < p ∧ (p : ℝ) ≤ S))).length +
      (l.filter (fun p : ℕ => decide (S < p ∧ (p : ℝ) ≤ n))).length = l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp.1
    have hn : (p : ℝ) ≤ n := by exact_mod_cast hp.2
    have hh := ih (fun q hq => hl q (by simp [hq]))
    by_cases hS : (p : ℝ) ≤ S
    · rw [List.filter_cons_of_pos (by exact decide_eq_true ⟨h1, hS⟩),
        List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using
          (show ¬ (S < (p : ℝ) ∧ (p : ℝ) ≤ n) from fun h => (not_lt.mpr hS) h.1)),
        List.length_cons]
      simp only [List.length_cons]
      omega
    · have hS' : S < (p : ℝ) := lt_of_not_ge hS
      rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using
          (show ¬ ((1 : ℝ) < p ∧ (p : ℝ) ≤ S) from fun h => hS h.2)),
        List.filter_cons_of_pos (by exact decide_eq_true ⟨hS', hn⟩),
        List.length_cons]
      simp only [List.length_cons]
      omega

lemma omegaIn_partition (n : ℕ) (S : ℝ) :
    omegaIn n 1 S + omegaIn n S n = n.primeFactorsList.length := by
  apply interval_count_partition
  intro p hp
  exact ⟨(Nat.prime_of_mem_primeFactorsList hp).one_lt, Nat.le_of_mem_primeFactorsList hp⟩

/-- Ford normality controls the full number of prime occurrences of a shift. -/
lemma normality_total_bound {S : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hSn : S < (p-1 : ℕ)) (hBS : 0 ≤ B S) :
    (p-1).primeFactorsList.length ≤ 3*B (p-1 : ℕ) := by
  have hn : (1 : ℝ) < (p-1 : ℕ) := hS.trans hSn
  have hB : B S ≤ B (p-1 : ℕ) := by
    apply Real.log_le_log (Real.log_pos hS)
    exact Real.log_le_log (zero_lt_one.trans hS) hSn.le
  have hBn : 0 ≤ B (p-1 : ℕ) := hBS.trans hB
  have hsqrt : Real.sqrt (B S*B (p-1 : ℕ)) ≤ B (p-1 : ℕ) := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hBn, by nlinarith⟩
  have hc := hp.2.2 S (p-1 : ℕ) le_rfl hSn le_rfl
  have hh := (abs_lt.mp hc).2
  have he := congrArg (fun n : ℕ => (n : ℝ)) (omegaIn_partition (p-1) S)
  push_cast at he
  linarith [hp.2.1]

lemma self_le_largest_pow_length {n : ℕ} (hn : n ≠ 0) :
    n ≤ (largestPrimeFactor n)^n.primeFactorsList.length := by
  calc
    n = n.primeFactorsList.prod := (Nat.prod_primeFactorsList hn).symm
    _ ≤ _ := List.prod_le_pow_length _ _ (fun p hp => primeFactor_le_largest hp)

lemma one_lt_largestPrimeFactor {n : ℕ} (hn : 2 ≤ n) : 1 < largestPrimeFactor n := by
  have h1 : 1 ≤ largestPrimeFactor n := le_max_left _ _
  have hpow := self_le_largest_pow_length (show n ≠ 0 by omega)
  by_contra hh
  have he : largestPrimeFactor n = 1 := by omega
  rw [he, one_pow] at hpow
  omega

/-- A bound for `Ω(n)` puts the largest prime factor within a logarithmic
distance of the double logarithm of `n`. -/
lemma largest_factor_doubleLog_lower {n : ℕ} {K : ℝ} (hn : 2 ≤ n) (hK : 0 < K)
    (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) :
    B n - Real.log K ≤ B (largestPrimeFactor n) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hA : (1 : ℝ) < largestPrimeFactor n := by
    exact_mod_cast one_lt_largestPrimeFactor hn
  have hp : (n : ℝ) ≤ (largestPrimeFactor n : ℝ)^n.primeFactorsList.length := by
    exact_mod_cast self_le_largest_pow_length (show n ≠ 0 by omega)
  have hl := Real.log_le_log (zero_lt_one.trans hnR) hp
  rw [Real.log_pow] at hl
  have hlu : Real.log (n : ℝ) ≤ K*Real.log (largestPrimeFactor n : ℝ) :=
    hl.trans (mul_le_mul_of_nonneg_right hΩ (Real.log_pos hA).le)
  have hdiv : Real.log (n : ℝ)/K ≤ Real.log (largestPrimeFactor n : ℝ) :=
    (div_le_iff₀ hK).mpr (by simpa [mul_comm] using hlu)
  have hh := Real.log_le_log (div_pos (Real.log_pos hnR) hK) hdiv
  simpa only [B, Real.log_div (Real.log_pos hnR).ne' hK.ne'] using hh

end TotientAsymptotic

end

end OAI
