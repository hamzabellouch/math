import OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting
import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalColumnRank
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

/-! The high-rank square-root saving dominates the full crude counting cost. -/

namespace TwoPointCorrelations

open Filter

lemma sqrt_pow_le_exp (β u : ℝ) (r : ℕ) (hβ : 0 ≤ β) (hbound : β ≤ Real.exp u) :
    Real.sqrt (β ^ r) ≤ Real.exp (u * r / 2) := by
  calc
    _ ≤ Real.sqrt ((Real.exp u) ^ r) :=
      Real.sqrt_le_sqrt (pow_le_pow_left₀ hβ hbound r)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_half]; congr 1; ring

/-- The logarithmic prime-divisor count contributes only its logarithm to
the exponent; the prime lower cutoff contributes the full negative term. -/
lemma reciprocal_rank_base_le (V H T D : ℝ) (M : ℕ)
    (hV : 1 ≤ V) (hH : Real.exp T ≤ H)
    (hM : 1 + (Nat.log 2 M : ℝ) ≤ Real.exp D) :
    (V * H)⁻¹ * (1 + (Nat.log 2 M : ℝ)) ≤ Real.exp (D - T) := by
  have hHp : 0 < H := (Real.exp_pos T).trans_le hH
  have hVH : Real.exp T ≤ V * H := by
    exact hH.trans (by nlinarith)
  have hi : (V * H)⁻¹ ≤ Real.exp (-T) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos T) hVH
  calc
    _ ≤ Real.exp (-T) * Real.exp D :=
      mul_le_mul hi hM (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Exponentially bounded integer coefficients have only linearly many
possible logarithmic prime-divisor slots. -/
lemma natLog_le_linear (M : ℕ) (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hM : (M : ℝ) ≤ Real.exp (A * L)) :
    (Nat.log 2 M : ℝ) ≤ A * L / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hzero : M = 0
  · simp only [hzero, Nat.log_zero_right, Nat.cast_zero]
    positivity
  have hMp : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hlog := Real.log_le_log hMp hM
  rw [Real.log_exp] at hlog
  apply (Real.natLog_le_logb M 2).trans
  exact div_le_div_of_nonneg_right hlog hlog2.le

lemma eventually_rank_log_budget (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ M : ℕ, (M : ℝ) ≤ Real.exp (A * L) →
      1 + (Nat.log 2 M : ℝ) ≤ Real.exp (2 * Real.log L) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_ge_atTop (1 + A / Real.log 2)] with L hL hlarge
  intro M hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := natLog_le_linear M A L hA (by linarith) hM
  have heq : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
    rw [show 2 * Real.log L = Real.log L + Real.log L by ring, Real.exp_add,
      Real.exp_log (by linarith : 0 < L)]
    ring
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ L by linarith)
  have hA' : 0 ≤ A / Real.log 2 := div_nonneg hA hlog2.le
  have hlog' : (Nat.log 2 M : ℝ) ≤ (A / Real.log 2) * L := by
    convert hlog using 1; ring
  nlinarith

/-- The actual coefficient bound `2 R h Q D B` is at most `exp (105 L)`
for the manuscript padding and other-column ranges. -/
lemma eventually_column_minor_size_exp (h : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ R Q D B : ℕ,
      (R : ℝ) ≤ 2 * L → (Q : ℝ) ≤ Real.exp (100 * L + 1) →
      (D : ℝ) ≤ Real.exp (2 * L) → (B : ℝ) ≤ Real.exp L →
      ((2 * R * (h * Q * D) * B : ℕ) : ℝ) ≤ Real.exp (105 * L) := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (4 * h * Real.exp 1)] with L hL hlarge
  intro R Q D B hR hQ hD hB
  have hconst : 4 * h * Real.exp 1 ≤ Real.exp L := by
    linarith [Real.add_one_le_exp L]
  have hlinear : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc
    _ ≤ 2 * (2 * L) * ((h : ℝ) * Real.exp (100 * L + 1) * Real.exp (2 * L)) * Real.exp L := by
      push_cast
      gcongr
    _ = (4 * h * Real.exp 1) * L *
        (Real.exp (100 * L) * Real.exp (2 * L) * Real.exp L) := by
      rw [Real.exp_add]
      ring
    _ = (4 * h * Real.exp 1) * L * Real.exp (103 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp L * Real.exp L * Real.exp (103 * L) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Quantitative form of `log² L = o(L^(3/200))`, multiplied by `L`. -/
lemma eventually_crude_cost_small (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, C * L * (Real.log L) ^ 2 ≤ (1 / 8 : ℝ) * L ^ (203 / 200 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (s := (3 / 200 : ℝ)) (by norm_num)).bound
      (show 0 < (1 / 8 : ℝ) / (C + 1) by positivity)
  filter_upwards [eventually_ge_atTop 1, h] with L hL hh
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hh
  have hscaled : C * (Real.log L) ^ 2 ≤ (1 / 8 : ℝ) * L ^ (3 / 200 : ℝ) := by
    calc
      _ ≤ (C + 1) * (Real.log L) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ (C + 1) * (((1 / 8 : ℝ) / (C + 1)) * L ^ (3 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by field_simp [(show C + 1 ≠ 0 by linarith)]
  have hm := mul_le_mul_of_nonneg_right hscaled hLp.le
  have hp : L ^ (203 / 200 : ℝ) = L ^ (3 / 200 : ℝ) * L := by
    calc
      _ = L ^ ((3 / 200 : ℝ) + 1) := by norm_num
      _ = _ := by rw [Real.rpow_add hLp, Real.rpow_one]
  rw [hp]
  nlinarith

/-- The floor in `r = floor(L^(1/50))` loses at most half the rank once
`L` is large; its upper bound is only `L`, sufficient for every overhead. -/
lemma eventually_rank_floor_bounds :
    ∀ᶠ L : ℝ in atTop,
      L ^ (1 / 50 : ℝ) / 2 ≤ (⌊L ^ (1 / 50 : ℝ)⌋₊ : ℝ) ∧
        (⌊L ^ (1 / 50 : ℝ)⌋₊ : ℝ) ≤ L := by
  have hr := (tendsto_rpow_atTop (show 0 < (1 / 50 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop 1, hr] with L hL hr
  have hpos : 0 ≤ L ^ (1 / 50 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hfloor := Nat.lt_floor_add_one (L ^ (1 / 50 : ℝ))
  constructor
  · linarith
  · exact (Nat.floor_le hpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hL (show (1 / 50 : ℝ) ≤ 1 by norm_num))

/-- The exact exponent `203/200 = 199/200 + 1/50` is retained. Fixed
coefficients in the crude enumeration only affect the threshold. -/
theorem eventually_high_rank_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ r : ℕ,
      L ^ (1 / 50 : ℝ) / 2 ≤ (r : ℝ) → (r : ℝ) ≤ L →
      Real.exp (C * L * (Real.log L) ^ 2) *
        Real.sqrt ((Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r) ≤
          Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_crude_cost_small (2 * C) (by positivity)] with L hL hlog hsmall
  intro r hrlo hrhi
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hp : L ^ (1 / 50 : ℝ) * L ^ (199 / 200 : ℝ) = L ^ (203 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hnegative := mul_le_mul_of_nonneg_right hrlo
    (show 0 ≤ L ^ (199 / 200 : ℝ) by positivity)
  have hpositive := mul_le_mul_of_nonneg_left hrhi (show 0 ≤ C * Real.log L by positivity)
  have hlog : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  have hover := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C * L by positivity)
  have hpositive' : C * Real.log L * r ≤ C * L * (Real.log L) ^ 2 := by
    calc
      _ ≤ C * Real.log L * L := hpositive
      _ = C * L * Real.log L := by ring
      _ ≤ _ := hover
  calc
    _ ≤ Real.exp (C * L * (Real.log L) ^ 2) *
        Real.exp ((C * Real.log L - L ^ (199 / 200 : ℝ)) * r / 2) :=
      mul_le_mul_of_nonneg_left (sqrt_pow_le_exp _ _ r (by positivity) le_rfl) (by positivity)
    _ = Real.exp (C * L * (Real.log L) ^ 2 +
        (C * Real.log L - L ^ (199 / 200 : ℝ)) * r / 2) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [div_mul_eq_mul_div, hp] at hnegative
      nlinarith [Real.rpow_nonneg hLp.le (203 / 200 : ℝ)]

/-- Numerical conclusion after summing the actual word records. The
coefficient of the counting exponent is fixed; it does not affect the
absolute decay exponent or constant. -/
theorem eventually_high_rank_total (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (r M : ℕ) (V H cost total : ℝ),
      L ^ (1 / 50 : ℝ) / 2 ≤ (r : ℝ) → (r : ℝ) ≤ L →
      1 ≤ V → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      1 + (Nat.log 2 M : ℝ) ≤ Real.exp (C * Real.log L) →
      0 ≤ cost → cost ≤ Real.exp (C * L * (Real.log L) ^ 2) →
      total ≤ cost * Real.sqrt (((V * H)⁻¹ * (1 + (Nat.log 2 M : ℝ))) ^ r) →
      total ≤ Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  filter_upwards [eventually_high_rank_decay C hC] with L hL
  intro r M V H cost total hrlo hrhi hV hH hM hcost hcost' htotal
  have hbase := reciprocal_rank_base_le V H (L ^ (199 / 200 : ℝ))
    (C * Real.log L) M hV hH hM
  have hVp : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hs : Real.sqrt (((V * H)⁻¹ * (1 + (Nat.log 2 M : ℝ))) ^ r) ≤
      Real.sqrt ((Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hbase r)
  apply htotal.trans
  calc
    _ ≤ cost * Real.sqrt ((Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r) :=
      mul_le_mul_of_nonneg_left hs hcost
    _ ≤ Real.exp (C * L * (Real.log L) ^ 2) *
        Real.sqrt ((Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r) :=
      mul_le_mul_of_nonneg_right hcost' (Real.sqrt_nonneg _)
    _ ≤ _ := hL r hrlo hrhi

end TwoPointCorrelations

end OAI
