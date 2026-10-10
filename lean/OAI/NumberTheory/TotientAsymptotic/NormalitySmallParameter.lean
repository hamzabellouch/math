import OAI.NumberTheory.TotientAsymptotic.PublishedNormality

namespace OAI

/-! The elementary parameter range in Ford's exceptional-prime estimate. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma prime_count_global_upper : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 < n →
    (Nat.primeCounting n : ℝ) ≤ C*n/Real.log n := by
  have hev : ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ (Real.log 4+1)*n/Real.log n := by
    have h := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
    simpa only [Nat.floor_natCast] using h
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  let C := max (Real.log 4+1) (2*Real.log (N+4:ℕ))
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < Real.log (4:ℝ)+1) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro n hn
  have hn' : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos hn'
  apply (le_div_iff₀ hlog).mpr
  by_cases hlarge : N ≤ n
  · have hh := (le_div_iff₀ hlog).mp (hN n hlarge)
    have hC' : Real.log 4+1 ≤ C := le_max_left _ _
    have hnc : (0:ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  · have hcount : (Nat.primeCounting n : ℝ) ≤ 2*n := by
      have hh : Nat.primeCounting n ≤ n+1 := Nat.count_le Nat.Prime
      exact_mod_cast (show Nat.primeCounting n ≤ 2*n by omega)
    have hnK : (n:ℝ) ≤ (N+4:ℕ) := by exact_mod_cast (show n ≤ N+4 by omega)
    have hlogK := Real.log_le_log (by linarith : (0:ℝ)<n) hnK
    have hC' : 2*Real.log (N+4:ℕ) ≤ C := le_max_right _ _
    have hh := mul_le_mul_of_nonneg_right hcount hlog.le
    nlinarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]

lemma doubleLog_nat_pos {n : ℕ} (hn : 3 < n) : 0 < B n := by
  unfold B
  apply Real.log_pos
  apply (Real.lt_log_iff_exp_lt (by positivity : (0:ℝ)<n)).mpr
  have hn' : (3:ℝ) < n := by exact_mod_cast hn
  exact Real.exp_one_lt_three.trans hn'

lemma normality_small_parameter_factor {S : ℝ} (hS : 2 < S) {n : ℕ} (hn : 3 < n)
    (hsmall : Real.log S ≤ (B n)^30) :
    1 ≤ (B n)^5*(Real.log S)^(-1/6:ℝ) := by
  have hlog : 0 < Real.log S := Real.log_pos (by linarith)
  have hB := doubleLog_nat_pos hn
  have hroot : (Real.log S)^(1/6:ℝ) ≤ (B n)^5 := by
    calc
      _ ≤ ((B n)^30)^(1/6:ℝ) := Real.rpow_le_rpow hlog.le hsmall (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
        norm_num
  rw [show (-1/6:ℝ) = -(1/6:ℝ) by norm_num, Real.rpow_neg hlog.le]
  exact (one_le_div (Real.rpow_pos_of_pos hlog _)).mpr hroot

/-- The desired exceptional-prime estimate holds throughout the small-S range
using only Chebyshev's bound. The hard range is isolated rather than assumed. -/
theorem normality_small_parameter : ∃ C : ℝ, 0 < C ∧
    ∀ S : ℝ, 2 < S → ∀ n : ℕ, 3 < n → Real.log S ≤ (B n)^30 →
      ((nonNormalPrimes S n).card : ℝ) ≤
        C*n/Real.log n*(B n)^5*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := prime_count_global_upper
  refine ⟨C,hC,?_⟩
  intro S hS n hn hsmall
  have hcount : ((nonNormalPrimes S n).card:ℝ) ≤ Nat.primeCounting n := by
    have hh := Finset.card_le_card (Finset.filter_subset (fun p => ¬IsNormalPrime S p) (Nat.primesLE n))
    rw [Nat.primesLE_card_eq_primeCounting] at hh
    exact_mod_cast hh
  apply hcount.trans ((hbound n hn).trans _)
  have hf := normality_small_parameter_factor hS hn hsmall
  have hbase : 0 ≤ C*n/Real.log n := by
    apply div_nonneg (by positivity)
    exact (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).le
  have hh := mul_le_mul_of_nonneg_left hf hbase
  simpa only [mul_one,mul_assoc] using hh

end TotientAsymptotic

end

end OAI
