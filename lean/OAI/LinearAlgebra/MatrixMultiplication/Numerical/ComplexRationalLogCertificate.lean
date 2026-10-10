import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.Foundation.RationalLogCertificate

open scoped BigOperators

noncomputable def sumPower (t : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, t ^ (i + 1) / (i + 1)

def rationalSumPower (t : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, t ^ (i + 1) / (i + 1)

noncomputable def realApprox (n : ℕ) (x : ℝ) : ℝ :=
  sumPower ((x - 1) / (x + 1)) n - sumPower (-((x - 1) / (x + 1))) n

def rationalApprox (n : ℕ) (x : ℚ) : ℚ :=
  rationalSumPower ((x - 1) / (x + 1)) n -
    rationalSumPower (-((x - 1) / (x + 1))) n

@[simp] theorem rationalSumPower_cast (t : ℚ) (n : ℕ) :
    (rationalSumPower t n : ℝ) = sumPower (t : ℝ) n := by
  simp [rationalSumPower, sumPower]

@[simp] theorem rationalApprox_cast (n : ℕ) (x : ℚ) :
    (rationalApprox n x : ℝ) = realApprox n (x : ℝ) := by
  simp [rationalApprox, realApprox]

theorem symmetric_expansion_error (t : ℝ) (ht : |t| < 1) (n : ℕ) :
    |(Real.log (1 + t) - Real.log (1 - t)) -
        (sumPower t n - sumPower (-t) n)| ≤
      2 * (|t| ^ (n + 1) / (1 - |t|)) := by
  have hminus : |sumPower t n + Real.log (1 - t)| ≤
      |t| ^ (n + 1) / (1 - |t|) :=
    Real.abs_log_sub_add_sum_range_le ht n
  have hplus : |sumPower (-t) n + Real.log (1 + t)| ≤
      |t| ^ (n + 1) / (1 - |t|) := by
    simpa only [sumPower, abs_neg, sub_neg_eq_add] using
      Real.abs_log_sub_add_sum_range_le (by simpa using ht : |-t| < 1) n
  calc
    _ = |(sumPower (-t) n + Real.log (1 + t)) -
        (sumPower t n + Real.log (1 - t))| := by congr 1; ring
    _ ≤ |sumPower (-t) n + Real.log (1 + t)| +
        |sumPower t n + Real.log (1 - t)| := abs_sub _ _
    _ ≤ 2 * (|t| ^ (n + 1) / (1 - |t|)) := by linarith

theorem normalized_variable_bounds (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    0 ≤ (x - 1) / (x + 1) ∧ (x - 1) / (x + 1) ≤ 1 / 3 := by
  have hden : 0 < x + 1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) hden.le
  · apply (div_le_iff₀ hden).2
    linarith

theorem normalized_log_error (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) (n : ℕ) :
    |Real.log x - realApprox n x| ≤
      2 * (((x - 1) / (x + 1)) ^ (n + 1) / (1 - (x - 1) / (x + 1))) := by
  let t := (x - 1) / (x + 1)
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hden : x + 1 ≠ 0 := by linarith
  have hminus : 1 - t ≠ 0 := by linarith
  have hplus : 1 + t ≠ 0 := by dsimp [t]; linarith
  have hratio : (1 + t) / (1 - t) = x := by
    dsimp [t]
    field_simp [hden]
    ring
  have hlog : Real.log x = Real.log (1 + t) - Real.log (1 - t) := by
    rw [← hratio]
    exact Real.log_div hplus hminus
  have ht0' : 0 ≤ t := ht0
  have herror := symmetric_expansion_error t (by rwa [abs_of_nonneg ht0']) n
  rw [abs_of_nonneg ht0'] at herror
  simpa only [realApprox, ← hlog, t] using herror

theorem normalized_log_error_80 (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    |Real.log x - realApprox 80 x| < 1 / (2 : ℝ) ^ 120 := by
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  apply lt_of_le_of_lt (normalized_log_error x hlo hhi 80)
  calc
    _ ≤ 2 * (((1 : ℝ) / 3) ^ 81 / (1 - 1 / 3)) := by gcongr
    _ < 1 / (2 : ℝ) ^ 120 := by norm_num

theorem rational_log_error_80 (x : ℚ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    |Real.log (x : ℝ) - (rationalApprox 80 x : ℝ)| < 1 / (2 : ℝ) ^ 120 := by
  rw [rationalApprox_cast]
  exact normalized_log_error_80 (x : ℝ) (by exact_mod_cast hlo) (by exact_mod_cast hhi)

structure ReducedArgument (x : ℚ) where
  exponent : ℤ
  mantissa : ℚ
  lower : 1 ≤ mantissa
  upper : mantissa ≤ 2
  value : x = mantissa * (2 : ℚ) ^ exponent

def reducedApprox {x : ℚ} (d : ReducedArgument x) : ℚ :=
  rationalApprox 80 d.mantissa + (d.exponent : ℚ) * rationalApprox 80 2

theorem ReducedArgument.positive {x : ℚ} (d : ReducedArgument x) : 0 < x := by
  rw [d.value]
  exact mul_pos (lt_of_lt_of_le (by norm_num) d.lower) (zpow_pos (by norm_num) _)

theorem reduced_log_error {x : ℚ} (d : ReducedArgument x) :
    |Real.log (x : ℝ) - (reducedApprox d : ℝ)| ≤
      (1 + |(d.exponent : ℝ)|) / (2 : ℝ) ^ 120 := by
  have hm : (0 : ℝ) < d.mantissa := by
    have hlo : (1 : ℝ) ≤ d.mantissa := by exact_mod_cast d.lower
    linarith
  have hvalue : (x : ℝ) = (d.mantissa : ℝ) * (2 : ℝ) ^ d.exponent := by
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℝ)) d.value
  have hlog : Real.log (x : ℝ) = Real.log (d.mantissa : ℝ) +
      (d.exponent : ℝ) * Real.log 2 := by
    rw [hvalue, Real.log_mul (ne_of_gt hm) (zpow_ne_zero _ (by norm_num)),
      Real.log_zpow]
  have hmerr := (rational_log_error_80 d.mantissa d.lower d.upper).le
  have htwoerr := (rational_log_error_80 2 (by norm_num) (by norm_num)).le
  have hcast : (reducedApprox d : ℝ) = (rationalApprox 80 d.mantissa : ℝ) +
      (d.exponent : ℝ) * (rationalApprox 80 2 : ℝ) := by
    simp [reducedApprox]
  rw [hlog, hcast]
  calc
    _ = |(Real.log (d.mantissa : ℝ) - (rationalApprox 80 d.mantissa : ℝ)) +
        (d.exponent : ℝ) * (Real.log 2 - (rationalApprox 80 2 : ℝ))| := by
      congr 1
      ring
    _ ≤ |Real.log (d.mantissa : ℝ) - (rationalApprox 80 d.mantissa : ℝ)| +
        |(d.exponent : ℝ)| * |Real.log 2 - (rationalApprox 80 2 : ℝ)| := by
      simpa only [abs_mul] using abs_add_le
        (Real.log (d.mantissa : ℝ) - (rationalApprox 80 d.mantissa : ℝ))
        ((d.exponent : ℝ) * (Real.log 2 - (rationalApprox 80 2 : ℝ)))
    _ ≤ 1 / (2 : ℝ) ^ 120 + |(d.exponent : ℝ)| * (1 / (2 : ℝ) ^ 120) := by
      exact add_le_add hmerr (mul_le_mul_of_nonneg_left htwoerr (abs_nonneg _))
    _ = (1 + |(d.exponent : ℝ)|) / (2 : ℝ) ^ 120 := by ring

theorem reduced_entropy_error {x : ℚ} (d : ReducedArgument x) :
    |(-(x : ℝ) * Real.log (x : ℝ)) - (-x * reducedApprox d : ℚ)| ≤
      (x : ℝ) * ((1 + |(d.exponent : ℝ)|) / (2 : ℝ) ^ 120) := by
  have hx : (0 : ℝ) ≤ x := by exact_mod_cast d.positive.le
  have hcast : ((-x * reducedApprox d : ℚ) : ℝ) = -(x : ℝ) * (reducedApprox d : ℝ) := by
    simp
  rw [hcast, ← mul_sub, abs_mul, abs_neg, abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_left (reduced_log_error d) hx

def finiteEntropyApprox {ι : Type*} [Fintype ι] (p : ι → ℚ)
    (d : ∀ i, ReducedArgument (p i)) : ℚ :=
  ∑ i, -p i * reducedApprox (d i)

theorem finite_entropy_error {ι : Type*} [Fintype ι] (p : ι → ℚ)
    (d : ∀ i, ReducedArgument (p i)) :
    |(∑ i, -(p i : ℝ) * Real.log (p i : ℝ)) - (finiteEntropyApprox p d : ℝ)| ≤
      ∑ i, (p i : ℝ) * ((1 + |((d i).exponent : ℝ)|) / (2 : ℝ) ^ 120) := by
  have hcast : (finiteEntropyApprox p d : ℝ) =
      ∑ i, ((-p i * reducedApprox (d i) : ℚ) : ℝ) := by
    simp [finiteEntropyApprox]
  rw [hcast, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(-(p i : ℝ) * Real.log (p i : ℝ)) -
        ((-p i * reducedApprox (d i) : ℚ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => reduced_entropy_error (d i))

theorem finite_entropy_error_of_exponent_bound {ι : Type*} [Fintype ι]
    (p : ι → ℚ) (d : ∀ i, ReducedArgument (p i))
    (hnorm : ∑ i, p i = 1) (K : ℝ)
    (hK : ∀ i, |((d i).exponent : ℝ)| ≤ K) :
    |(∑ i, -(p i : ℝ) * Real.log (p i : ℝ)) - (finiteEntropyApprox p d : ℝ)| ≤
      (1 + K) / (2 : ℝ) ^ 120 := by
  apply (finite_entropy_error p d).trans
  have hnorm' : ∑ i, (p i : ℝ) = 1 := by exact_mod_cast hnorm
  calc
    _ ≤ ∑ i, (p i : ℝ) * ((1 + K) / (2 : ℝ) ^ 120) := by
      apply Finset.sum_le_sum
      intro i _
      have hp : (0 : ℝ) ≤ p i := by exact_mod_cast (d i).positive.le
      apply mul_le_mul_of_nonneg_left _ hp
      exact div_le_div_of_nonneg_right (add_le_add_right (hK i) 1) (by positivity)
    _ = (1 + K) / (2 : ℝ) ^ 120 := by rw [← Finset.sum_mul, hnorm', one_mul]

end MatrixMultiplication.Foundation.RationalLogCertificate

end OAI
