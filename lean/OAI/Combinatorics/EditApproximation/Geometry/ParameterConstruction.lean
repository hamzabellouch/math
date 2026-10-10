import OAI.Combinatorics.EditApproximation.Binary.IntegerPreprocessing
import OAI.Combinatorics.EditApproximation.Refinement.ComputedSourceAddressBits
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Counted register loops for the global integer parameters. Multiplication
and division here are word operations; the word-cap theorem below supplies
room for their intermediate integers. -/
namespace EditApproximation
open Filter

 theorem size_pred_eq_clog_two (n : ℕ) : (n - 1).size = Nat.clog 2 n := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.size_le, Nat.clog_le_iff_le_pow (by decide)]
  have hp := Nat.two_pow_pos k
  omega

 theorem size_pred_eq_log_two (n : ℕ) : n.size - 1 = Nat.log 2 n := by
  by_cases hn : n = 0
  · subst n; simp
  apply eq_of_forall_le_iff
  intro k
  have hs : 0 < n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [Nat.le_log_iff_pow_le (by decide) hn]
  have hk := Nat.lt_size (m := k) (n := n)
  omega



 @[simp] theorem parameterClogWithWork_spec (n : ℕ) :
    parameterClogWithWork n = (Nat.clog 2 n, 2 * Nat.clog 2 n + 3) := by
  simp only [parameterClogWithWork, inputBitLengthWithWork_spec, size_pred_eq_clog_two]



 @[simp] theorem parameterLogWithWork_value (n : ℕ) :
    (parameterLogWithWork n).1 = Nat.log 2 n := by
  simp only [parameterLogWithWork, inputBitLengthWithWork_spec, size_pred_eq_log_two]

 theorem parameterLogWithWork_cost (n : ℕ) :
    (parameterLogWithWork n).2 = 2 * n.size + 2 := by
  simp only [parameterLogWithWork, inputBitLengthWithWork_spec]



 theorem parameterRootSearch_value (n k : ℕ) (hk : n.sqrt ≤ k) :
    (parameterRootSearch n k).1 = n.sqrt := by
  induction k with
  | zero => simp only [parameterRootSearch]; omega
  | succ k ih =>
    rw [parameterRootSearch]
    split_ifs with h
    · have := Nat.le_sqrt.mpr h
      dsimp only
      omega
    · have hk' : n.sqrt ≤ k := by
        have := Nat.le_sqrt.not.mpr h
        omega
      exact ih hk'

 theorem parameterRootSearch_cost (n k : ℕ) :
    (parameterRootSearch n k).2 ≤ 3 * k + 1 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [parameterRootSearch]
    split_ifs <;> dsimp only <;> omega



 @[simp] theorem parameterSqrtWithWork_value (n : ℕ) :
    (parameterSqrtWithWork n).1 = n.sqrt :=
  parameterRootSearch_value n n (Nat.sqrt_le_self n)

 theorem parameterSqrtWithWork_cost (n : ℕ) :
    (parameterSqrtWithWork n).2 ≤ 3 * n + 1 := parameterRootSearch_cost n n



 @[simp] theorem parameterPowerWithWork_spec (a k : ℕ) :
    parameterPowerWithWork a k = (a ^ k, 2 * k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [parameterPowerWithWork, ih, pow_succ]; congr 1

 theorem parameterPowerWithWork_intermediate (a k j : ℕ) (ha : 1 ≤ a) (hj : j ≤ k) :
    (parameterPowerWithWork a j).1 ≤ a ^ k := by
  rw [parameterPowerWithWork_spec]
  exact Nat.pow_le_pow_right (by omega) hj



 @[simp] theorem integerParametersWithWork_value (N : ℕ) :
    (integerParametersWithWork N).1 = integerParameters N := by
  simp only [integerParametersWithWork, parameterClogWithWork_spec, parameterPowerWithWork_spec,
    parameterLogWithWork_value, parameterSqrtWithWork_value, integerParameters,
    heightExponent, inputHeight, smallLogExponent, inputSmallLog, coarseExponent]

 theorem integerParametersWithWork_cost (N : ℕ) :
    (integerParametersWithWork N).2 ≤ 1000 * (inputHeight N + 1) := by
  have hfirst : Nat.clog 2 (N + 2) ≤ inputHeight N :=
    Nat.clog_le_of_le_pow (inputHeight_covers_length N)
  have he : heightExponent N ≤ inputHeight N := Nat.lt_two_pow_self.le
  have hs : smallLogExponent N ≤ inputHeight N :=
    (Nat.lt_two_pow_self.le : smallLogExponent N ≤ inputSmallLog N).trans
      (computed_smallLog_le_height N)
  have hp : coarseExponent (inputSmallLog N) ≤ inputHeight N :=
    (coarseExponent_le_smallLog N).trans (computed_smallLog_le_height N)
  have hl : Nat.log 2 (inputSmallLog N) ≤ inputHeight N :=
    (Nat.log_le_self _ _).trans (computed_smallLog_le_height N)
  have hr : (Nat.log 2 (inputSmallLog N)).sqrt ≤ inputHeight N :=
    (Nat.sqrt_le_self _).trans hl
  have hlogsize : (inputSmallLog N).size ≤ inputHeight N + 1 := by
    change (2 ^ smallLogExponent N).size ≤ _
    rw [Nat.size_pow]
    omega
  have hroot := parameterSqrtWithWork_cost (Nat.log 2 (inputSmallLog N))
  have hroot2 := parameterSqrtWithWork_cost ((Nat.log 2 (inputSmallLog N)).sqrt)
  have hlogcost := parameterLogWithWork_cost (inputSmallLog N)
  simp only [integerParametersWithWork, parameterClogWithWork_spec, parameterPowerWithWork_spec,
    parameterLogWithWork_value, parameterSqrtWithWork_value]
  change 2 * Nat.clog 2 (N + 2) + 3 + (2 * heightExponent N + 3) + (2 * heightExponent N + 1) +
    (2 * smallLogExponent N + 3) + (2 * smallLogExponent N + 1) +
    (parameterLogWithWork (inputSmallLog N)).2 +
    (parameterSqrtWithWork (Nat.log 2 (inputSmallLog N))).2 +
    (parameterSqrtWithWork ((Nat.log 2 (inputSmallLog N)).sqrt)).2 +
    (2 * (heightExponent N / 20) + 1) + (2 * coarseExponent (inputSmallLog N) + 1) +
    (2 * (coarseExponent (inputSmallLog N) + 4) + 1) +
    (2 * (coarseExponent (inputSmallLog N) + 20) + 1) +
    (2 * ((3 * heightExponent N + 3) / 4) + 1) + (2 * 2 + 1) + 15 ≤ _
  have hdiv := Nat.div_le_self (heightExponent N) 20
  have hdiv' := Nat.div_le_self (3 * heightExponent N + 3) 4
  omega

 theorem integerParameter_power_word_cap :
    ∀ᶠ N in atTop,
      Nat.size (inputHeight N ^ (coarseExponent (inputSmallLog N) + 20)) ≤ inputHeight N := by
  filter_upwards [computed_sourceAddressBits_le_height 20] with N hN
  apply (natural_power_bit_length _ _).trans
  have hpow : coarseExponent (inputSmallLog N) + 20 ≤
      20 * (coarseExponent (inputSmallLog N) + 1) := by omega
  exact (Nat.add_le_add_right (Nat.mul_le_mul_right _ hpow) 1).trans hN

 theorem parameterPowerWithWork_word_cap (a k W : ℕ) (ha : 1 ≤ a)
    (hcap : Nat.size (a ^ k) ≤ W) (j : ℕ) (hj : j ≤ k) :
    (parameterPowerWithWork a j).1 < 2 ^ W :=
  (parameterPowerWithWork_intermediate a k j ha hj).trans_lt (Nat.size_le.mp hcap)

 theorem parameterRootSearch_word_cap (n k W : ℕ) (hk : k ≤ n)
    (hcap : n * n < 2 ^ W) : k * k < 2 ^ W :=
  (Nat.mul_le_mul hk hk).trans_lt hcap

end EditApproximation

end OAI
