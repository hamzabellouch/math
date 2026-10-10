import OAI.NumberTheory.Ostmann.Construction.InitialLogSumBins

namespace OAI

/-! # Uniform exponential mass of the chosen broad-band cutoff -/

namespace Ostmann
open scoped Classical BigOperators

theorem logSumCenter_count_bound (n m : ℕ) (T : ℝ)
    (hm : 1 ≤ m) (hn : n ≤ m) (hT : T ≤ m) :
    (⌈(n : ℝ) * Real.exp T⌉₊ : ℝ) + 1 ≤ Real.exp (2 * m) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
  have he : (m : ℝ) + 1 ≤ Real.exp m := by
    linarith [Real.add_one_le_exp (m : ℝ)]
  have he2 : (2 : ℝ) ≤ Real.exp m := by linarith
  calc
    _ ≤ (n : ℝ) * Real.exp T + 2 := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) * Real.exp T by positivity)
      linarith
    _ ≤ (m : ℝ) * Real.exp m + 2 := by gcongr
    _ ≤ ((m : ℝ) + 1) * Real.exp m := by nlinarith
    _ ≤ Real.exp m * Real.exp m := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem halfPower_div_logSumCenters (n m : ℕ) (T : ℝ)
    (hm : 1 ≤ m) (hn : n ≤ m) (hT : T ≤ m) :
    Real.exp (-(Real.log 2 + 2) * m) ≤
      (1 / 2 : ℝ) ^ n / ((⌈(n : ℝ) * Real.exp T⌉₊ : ℝ) + 1) := by
  have hcount := logSumCenter_count_bound n m T hm hn hT
  have hpow : Real.exp (-(Real.log 2) * m) ≤ (1 / 2 : ℝ) ^ n := by
    have he : Real.exp (-(Real.log 2) * n) = (1 / 2 : ℝ) ^ n := by
      rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp only [one_div, inv_pow]
    rw [← he]
    apply Real.exp_le_exp.mpr
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
    nlinarith
  have hform : Real.exp (-(Real.log 2 + 2) * m) =
      Real.exp (-(Real.log 2) * m) / Real.exp (2 * m) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hform]
  exact div_le_div₀ (by positivity) hpow (by positivity) hcount

/-- A literal logarithmic-sum weight with mass at least `exp(-C m)`.
The constant is independent of the later gap parameters and transfer depth. -/
theorem exists_balanced_prime_log_sum_center (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n m : ℕ) (T : ℝ)
    (μ : Fin n → P → ℝ) (good : Fin n → P → Prop)
    (hm : 1 ≤ m) (hn : n ≤ m) (hT : T ≤ m)
    (hlog : ∀ p : P, Real.log (p : ℝ) ≤ Real.exp T)
    (hmass : ∀ i, (1 / 2 : ℝ) ≤ ∑ p, if good i p then μ i p else 0) :
    ∃ c ∈ Finset.Icc (0 : ℤ) ⌈(n : ℝ) * Real.exp T⌉₊,
      Real.exp (-(Real.log 2 + 2) * m) ≤
        ∑ x ∈ balancedTupleSet n good, productPrior μ x *
          logCellProfile ((∑ i, Real.log (x i : ℝ)) - c) := by
  have hscore (x : Fin n → P) : 0 ≤ ∑ i, Real.log (x i : ℝ) ∧
      (∑ i, Real.log (x i : ℝ)) ≤ (⌈(n : ℝ) * Real.exp T⌉₊ : ℝ) := by
    constructor
    · exact Finset.sum_nonneg (fun i _ => Real.log_nonneg
        (by exact_mod_cast (hP (x i) (x i).property).one_lt.le))
    · calc
        _ ≤ ∑ _i : Fin n, Real.exp T := Finset.sum_le_sum (fun i _ => hlog (x i))
        _ = (n : ℝ) * Real.exp T := by simp
        _ ≤ _ := Nat.le_ceil _
  obtain ⟨c, hc, h⟩ := exists_balanced_log_sum_center n μ good
    (fun x => ∑ i, Real.log (x i : ℝ)) ⌈(n : ℝ) * Real.exp T⌉₊
    (1 / 2) (by norm_num) hmass hscore
  exact ⟨c, hc, (halfPower_div_logSumCenters n m T hm hn hT).trans h⟩

end Ostmann

end OAI
