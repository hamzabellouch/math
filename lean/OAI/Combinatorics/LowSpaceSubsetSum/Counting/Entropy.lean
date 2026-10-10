import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import OAI.Probability.TraceReconstruction.Binomial

namespace OAI

/-!
# Binary entropy estimates used by the subset-sum algorithm

The paper measures entropy in bits, whereas Mathlib's `Real.binEntropy`
uses natural logarithms. Normalization gives the elementary estimates in
the paper's preliminary section.
-/

namespace LowSpaceSubsetSum

/-- Binary entropy measured in bits. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

private theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem binaryEntropy_eq_logb (p : ℝ) :
    binaryEntropy p = p * Real.logb 2 p⁻¹ + (1 - p) * Real.logb 2 (1 - p)⁻¹ := by
  unfold binaryEntropy Real.binEntropy Real.logb
  ring

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy]

@[simp] theorem binaryEntropy_half : binaryEntropy (1 / 2) = 1 := by
  simpa only [one_div] using
    (show binaryEntropy (2⁻¹) = 1 by
      simp [binaryEntropy, ne_of_gt log_two_pos])

@[simp] theorem binaryEntropy_one_sub (p : ℝ) :
    binaryEntropy (1 - p) = binaryEntropy p := by
  simp [binaryEntropy]

theorem binaryEntropy_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binaryEntropy p :=
  div_nonneg (Real.binEntropy_nonneg hp0 hp1) log_two_pos.le

theorem binaryEntropy_le_one (p : ℝ) : binaryEntropy p ≤ 1 := by
  exact (div_le_one log_two_pos).mpr Real.binEntropy_le_log_two

theorem binaryEntropy_concaveOn : ConcaveOn ℝ (Set.Icc 0 1) binaryEntropy := by
  convert Real.strictConcave_binEntropy.concaveOn.smul
    (inv_nonneg.mpr log_two_pos.le) using 1
  ext p
  simp only [binaryEntropy, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem binaryEntropy_strictMonoOn :
    StrictMonoOn binaryEntropy (Set.Icc 0 (1 / 2)) := by
  intro x hx y hy hxy
  exact (div_lt_div_iff_of_pos_right log_two_pos).mpr
    (Real.binEntropy_strictMonoOn (by simpa only [one_div] using hx)
      (by simpa only [one_div] using hy) hxy)

theorem binaryEntropy_monoOn : MonotoneOn binaryEntropy (Set.Icc 0 (1 / 2)) :=
  binaryEntropy_strictMonoOn.monotoneOn

private theorem logb_two_self : Real.logb 2 2 = 1 :=
  Real.logb_self_eq_one (by norm_num)

private theorem logb_two_four : Real.logb 2 4 = 2 := by
  have h := Real.logb_pow 2 2 2
  norm_num [logb_two_self] at h ⊢
  exact h

theorem binaryEntropy_quarter :
    binaryEntropy (1 / 4) = 2 - (3 / 4) * Real.logb 2 3 := by
  rw [binaryEntropy_eq_logb]
  norm_num only [show (1 - (1 / 4 : ℝ)) = 3 / 4 by norm_num,
    show (1 / 4 : ℝ)⁻¹ = 4 by norm_num,
    show (3 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num]
  rw [Real.logb_div (by norm_num) (by norm_num), logb_two_four]
  ring

theorem binaryEntropy_third :
    binaryEntropy (1 / 3) = Real.logb 2 3 - 2 / 3 := by
  rw [binaryEntropy_eq_logb]
  norm_num only [show (1 - (1 / 3 : ℝ)) = 2 / 3 by norm_num,
    show (1 / 3 : ℝ)⁻¹ = 3 by norm_num,
    show (2 / 3 : ℝ)⁻¹ = 3 / 2 by norm_num]
  rw [Real.logb_div (by norm_num) (by norm_num), logb_two_self]
  ring

theorem binaryEntropy_quarter_complement :
    (3 / 4) * binaryEntropy (1 / 3) - 1 / 2 = 1 - binaryEntropy (1 / 4) := by
  rw [binaryEntropy_third, binaryEntropy_quarter]
  ring

theorem binaryEntropy_sixth :
    binaryEntropy (1 / 6) =
      (1 / 6) * Real.logb 2 6 + (5 / 6) * Real.logb 2 (6 / 5) := by
  rw [binaryEntropy_eq_logb]
  norm_num

/-- The integer power comparison certifying the paper's decimal entropy bound. -/
theorem binaryEntropy_quarter_lt : binaryEntropy (1 / 4) < 4057 / 5000 := by
  have h := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (2 : ℝ) ^ 84)
    (by norm_num : (2 : ℝ) ^ 84 < 3 ^ 53)
  rw [Real.logb_pow, Real.logb_pow, logb_two_self] at h
  norm_num at h
  rw [binaryEntropy_quarter]
  linarith

theorem binaryEntropy_third_lt : binaryEntropy (1 / 3) < 14 / 15 := by
  have h := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (3 : ℝ) ^ 5)
    (by norm_num : (3 : ℝ) ^ 5 < 2 ^ 8)
  rw [Real.logb_pow, Real.logb_pow, logb_two_self] at h
  norm_num at h
  rw [binaryEntropy_third]
  linarith

theorem binaryEntropy_sixth_gt : 5 / 8 < binaryEntropy (1 / 6) := by
  have h6 := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (2 : ℝ) ^ 5)
    (by norm_num : (2 : ℝ) ^ 5 < 6 ^ 2)
  have h65 := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
    (by norm_num : 0 < (2 : ℝ))
    (by norm_num : (2 : ℝ) < (6 / 5) ^ 4)
  rw [Real.logb_pow, Real.logb_pow, logb_two_self] at h6
  rw [Real.logb_pow, logb_two_self] at h65
  norm_num at h6 h65
  rw [binaryEntropy_sixth]
  linarith

/-- The paired entropy budget in the representation tree is maximized
when the two cardinality densities coincide. -/
theorem binaryEntropy_pair_le_quarter {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (binaryEntropy p + binaryEntropy (1 / 2 - p)) / 2 ≤ binaryEntropy (1 / 4) := by
  have h := binaryEntropy_concaveOn.2
    (show p ∈ Set.Icc 0 1 from ⟨hp0, by linarith⟩)
    (show 1 / 2 - p ∈ Set.Icc 0 1 from ⟨by linarith, by linarith⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num only [smul_eq_mul] at h
  convert h using 1 <;> congr 1 <;> ring

/-- The two child entropy values differ by less than the paper's `3/8`
margin throughout the allowed density interval. -/
theorem binaryEntropy_abs_sub_lt {p q : ℝ} (hp : p ∈ Set.Icc (1 / 6) (1 / 3))
    (hq : q ∈ Set.Icc (1 / 6) (1 / 3)) :
    |binaryEntropy p - binaryEntropy q| < 3 / 8 := by
  have hp_lower := binaryEntropy_monoOn (show (1 / 6 : ℝ) ∈ Set.Icc 0 (1 / 2)
      by norm_num) (show p ∈ Set.Icc 0 (1 / 2) from ⟨by linarith [hp.1], by linarith [hp.2]⟩)
    hp.1
  have hq_lower := binaryEntropy_monoOn (show (1 / 6 : ℝ) ∈ Set.Icc 0 (1 / 2)
      by norm_num) (show q ∈ Set.Icc 0 (1 / 2) from ⟨by linarith [hq.1], by linarith [hq.2]⟩)
    hq.1
  rw [abs_lt]
  constructor <;> linarith [binaryEntropy_le_one p, binaryEntropy_le_one q,
    binaryEntropy_sixth_gt]

open scoped BigOperators

/-- The binomial mass at its integral mean lies between `1/(n+1)` and `1`. -/
theorem binomialMass_mean_bounds (n k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hk : k ≤ n) (hmean : (n : ℝ) * p = k) :
    1 ≤ ((n : ℝ) + 1) * TraceReconstruction.binomialMass n p k ∧
      TraceReconstruction.binomialMass n p k ≤ 1 := by
  have hnonneg (j : ℕ) := TraceReconstruction.binomialMass_nonneg n j
    (show p ∈ Set.Icc 0 1 from ⟨hp.1.le, hp.2.le⟩)
  constructor
  · have hs := Finset.sum_le_sum (s := Finset.range (n + 1))
      (fun j _ => TraceReconstruction.binomialMass_le_mode n k j hp hk hmean)
    simpa only [TraceReconstruction.sum_binomialMass, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hs
  · have hs := Finset.single_le_sum (fun j _ => hnonneg j)
      (Finset.mem_range.mpr (show k < n + 1 by omega))
    simpa only [TraceReconstruction.sum_binomialMass] using hs

/-- The inverse of the entropy power is the probability of an individual
binary string with `k` successes, when the Bernoulli parameter is `k/n`. -/
theorem binomialMass_eq_choose_div_entropy (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    TraceReconstruction.binomialMass n ((k : ℝ) / n) k =
      (n.choose k : ℝ) / (2 : ℝ) ^ ((n : ℝ) * binaryEntropy ((k : ℝ) / n)) := by
  let p : ℝ := (k : ℝ) / n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_trans hk0 hkn)
  have hp0 : 0 < p := div_pos (by exact_mod_cast hk0) hn0
  have hp1 : p < 1 := (div_lt_one hn0).mpr (by exact_mod_cast hkn)
  have hmean : (n : ℝ) * p = k := by
    dsimp [p]
    field_simp [ne_of_gt hn0]
  have hprod : p ^ k * (1 - p) ^ (n - k) =
      Real.exp (-(n : ℝ) * Real.binEntropy p) := by
    conv_lhs => rw [← Real.exp_log (pow_pos hp0 k),
      ← Real.exp_log (pow_pos (sub_pos.mpr hp1) (n - k))]
    rw [← Real.exp_add]
    congr 1
    rw [Real.log_pow, Real.log_pow, Real.binEntropy, Real.log_inv, Real.log_inv,
      Nat.cast_sub hkn.le]
    linear_combination (Real.log (1 - p) - Real.log p) * hmean
  have hpower : (2 : ℝ) ^ ((n : ℝ) * binaryEntropy p) =
      Real.exp ((n : ℝ) * Real.binEntropy p) := by
    rw [Real.rpow_def_of_pos (by norm_num), binaryEntropy]
    congr 1
    field_simp [ne_of_gt log_two_pos]
  change TraceReconstruction.binomialMass n p k = _
  unfold TraceReconstruction.binomialMass
  rw [mul_assoc, hprod, hpower, div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

/-- Exact entropy bounds for binomial coefficients, including both endpoints. -/
theorem choose_entropy_bounds (n k : ℕ) (hk : k ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) * binaryEntropy ((k : ℝ) / n)) / ((n : ℝ) + 1) ≤
        (n.choose k : ℝ) ∧
      (n.choose k : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binaryEntropy ((k : ℝ) / n)) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.cast_zero, zero_div, binaryEntropy_zero, mul_zero, Real.rpow_zero,
      Nat.choose_zero_right, Nat.cast_one, le_refl, and_true]
    exact (div_le_one hn1).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  by_cases hkn : k = n
  · subst k
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hk0
    simp only [div_self hn0, binaryEntropy_one, mul_zero, Real.rpow_zero,
      Nat.choose_self, Nat.cast_one, le_refl, and_true]
    exact (div_le_one hn1).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hkn' : k < n := lt_of_le_of_ne hk hkn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_trans (Nat.pos_of_ne_zero hk0) hkn')
  have hp : (k : ℝ) / n ∈ Set.Ioo 0 1 :=
    ⟨div_pos (by exact_mod_cast Nat.pos_of_ne_zero hk0) hn0,
      (div_lt_one hn0).mpr (by exact_mod_cast hkn')⟩
  have hmean : (n : ℝ) * ((k : ℝ) / n) = k := by field_simp [ne_of_gt hn0]
  obtain ⟨hl, hu⟩ := binomialMass_mean_bounds n k hp hk hmean
  rw [binomialMass_eq_choose_div_entropy n k (Nat.pos_of_ne_zero hk0) hkn'] at hl hu
  have hpower : 0 < (2 : ℝ) ^ ((n : ℝ) * binaryEntropy ((k : ℝ) / n)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · rw [← mul_div_assoc] at hl
    have h := (le_div_iff₀ hpower).mp hl
    exact (div_le_iff₀ hn1).mpr (by simpa only [one_mul, mul_comm] using h)
  · exact (div_le_one hpower).mp hu

/-- Logarithmic form used in the background allocation formulas. -/
theorem logb_choose_bounds (n k : ℕ) (hk : k ≤ n) :
    (n : ℝ) * binaryEntropy ((k : ℝ) / n) - Real.logb 2 ((n : ℝ) + 1) ≤
        Real.logb 2 (n.choose k) ∧
      Real.logb 2 (n.choose k) ≤ (n : ℝ) * binaryEntropy ((k : ℝ) / n) := by
  obtain ⟨hl, hu⟩ := choose_entropy_bounds n k hk
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpower : 0 < (2 : ℝ) ^ ((n : ℝ) * binaryEntropy ((k : ℝ) / n)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (div_pos hpower hn1) hl
    simpa only [Real.logb_div (ne_of_gt hpower) (ne_of_gt hn1),
      Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using h
  · have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (show (0 : ℝ) < n.choose k by exact_mod_cast Nat.choose_pos hk) hu
    simpa only [Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)] using h

/-- Rounding the binomial logarithm costs less than `log₂(n+1)+1` bits. -/
theorem floor_logb_choose_error (n k : ℕ) (hk : k ≤ n) :
    |((⌊Real.logb 2 (n.choose k)⌋ : ℤ) : ℝ) -
      (n : ℝ) * binaryEntropy ((k : ℝ) / n)| < Real.logb 2 ((n : ℝ) + 1) + 1 := by
  obtain ⟨hl, hu⟩ := logb_choose_bounds n k hk
  have hf := Int.floor_le (Real.logb 2 (n.choose k))
  have hfloor := Int.sub_one_lt_floor (Real.logb 2 (n.choose k))
  rw [abs_of_nonpos (by linarith)]
  linarith

end LowSpaceSubsetSum

end OAI
