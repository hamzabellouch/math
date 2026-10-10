import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace OAI

/-! Numerical estimates used in the fixed-length binary conversion. -/

open Filter Asymptotics

namespace TreeEdit.BinaryLower.Code

/-- The segment threshold used in the prescribed-length code construction. -/
noncomputable def segmentThreshold (M : ℕ) : ℕ :=
  Nat.ceil (120 * Real.logb 2 (M : ℝ))

/-- Eventually the error from the short block-pair spans fits within half a block. -/
theorem eventually_short_pair_error :
    ∀ᶠ M : ℕ in atTop,
      0 < M ∧ 2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2 := by
  have hlog : (fun M : ℕ => Real.logb 2 (M : ℝ)) =o[atTop]
      (fun M : ℕ => (M : ℝ)) :=
    (Real.isLittleO_logb_id_atTop (b := 2)).comp_tendsto
      tendsto_natCast_atTop_atTop
  have hb := hlog.bound (show (0 : ℝ) < 1 / 960 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (8 : ℕ)] with M hM h8
  have hpos : 0 < M := by omega
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast h8
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hlog0 : 0 ≤ Real.logb 2 (M : ℝ) :=
    Real.logb_nonneg (by norm_num) hM1
  have hlogbound : Real.logb 2 (M : ℝ) ≤ (1 / 960 : ℝ) * M := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hM0] using hM
  have hceil : (segmentThreshold M : ℝ) < 120 * Real.logb 2 (M : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hsmall : (segmentThreshold M : ℝ) ≤ (M : ℝ) / 4 := by
    linarith
  refine ⟨hpos, ?_⟩
  have := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 * (M : ℝ) by positivity)
  nlinarith

/-- An absolute integer threshold exists, as required in the manuscript. -/
theorem exists_short_pair_threshold :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      0 < M ∧ 2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2 := by
  exact eventually_atTop.1 eventually_short_pair_error

/-- Removing the additive error in the block-matching estimate gives the
constant 402. The nonzero original deficit is integral, hence at least one. -/
theorem deficit_from_additive {P r δ e : ℝ}
    (hP : 0 ≤ P) (hr : 1 ≤ r)
    (hadd : P * r ≤ 201 * δ + e) (herr : e ≤ P / 2) :
    P / 402 * r ≤ δ := by
  have hPr : P ≤ P * r := by nlinarith
  nlinarith

/-- Combining the deficit inequality with the two ordinary-edit comparisons
produces exactly the constant 804, without changing the edit metric. -/
theorem edit_lower_from_deficit {P r r' d d' : ℝ}
    (hP : 0 ≤ P) (hdeficit : P / 402 * r ≤ r')
    (hleft : r' ≤ d') (hright : d ≤ 2 * r) :
    P / 804 * d ≤ d' := by
  have := mul_le_mul_of_nonneg_left hright (show 0 ≤ P / 804 by positivity)
  nlinarith

/-- The equal-label and unequal-label counts combine into the additive
estimate. All quantities are natural cardinalities, so no rounding is hidden. -/
theorem block_counts_to_additive {M P a₀ L r matched equal unequal δ : ℕ}
    (hpartition : matched = equal + unequal)
    (htotal : matched + δ = M * P)
    (hdeficit : r + L = M)
    (hequal : equal ≤ P * L)
    (hunequal : unequal ≤ 200 * δ + 2 * M * a₀) :
    P * r ≤ 201 * δ + 2 * M * a₀ := by
  nlinarith

/-- Integral form of the error absorption, including the zero-deficit case. -/
theorem natural_deficit_from_additive {P r δ e : ℕ}
    (hadd : P * r ≤ 201 * δ + e) (herr : 2 * e ≤ P) :
    P * r ≤ 402 * δ := by
  by_cases hr : r = 0
  · simp [hr]
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
  have hPr : P ≤ P * r := by nlinarith
  nlinarith

/-- Cast the integral matching conclusion into the exact real-valued lower
bound used in the statement of the fixed-length conversion theorem. -/
theorem real_deficit_of_natural {P r δ : ℕ}
    (h : P * r ≤ 402 * δ) :
    (P : ℝ) / 402 * r ≤ δ := by
  have h' : (P : ℝ) * r ≤ 402 * δ := by exact_mod_cast h
  linarith

/-- The two common formulas for the segment threshold agree at positive M. -/
theorem segmentThreshold_eq (M : ℕ) :
    segmentThreshold M =
      Nat.ceil (40 * Real.logb 2 ((M : ℝ) ^ 3)) := by
  unfold segmentThreshold
  rw [Real.logb_pow]
  congr 1
  ring

/-- Elementary failure tail at the source logarithmic segment threshold. -/
theorem code_failure_power_bound {M : ℕ} (hM : 1 ≤ M) :
    (9 / 10 : ℝ) ^ segmentThreshold M * (M : ℝ) ^ 12 ≤ 1 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hlog0 := Real.log_nonneg hM1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    exact this
  have hlogbase : Real.log (M : ℝ) ≤ Real.logb 2 (M : ℝ) := by
    rw [Real.logb, le_div_iff₀ hlog2pos]
    nlinarith
  have hthreshold : 120 * Real.log (M : ℝ) ≤ (segmentThreshold M : ℝ) := by
    have hceil := Nat.le_ceil (120 * Real.logb 2 (M : ℝ))
    change 120 * Real.logb 2 (M : ℝ) ≤ (segmentThreshold M : ℝ) at hceil
    linarith
  have hbase : (9 / 10 : ℝ) ≤ Real.exp (-(1 / 10 : ℝ)) := by
    have := Real.add_one_le_exp (-(1 / 10 : ℝ))
    linarith
  have htail : (9 / 10 : ℝ) ^ segmentThreshold M ≤
      Real.exp (-(12 * Real.log (M : ℝ))) := by
    calc
      (9 / 10 : ℝ) ^ segmentThreshold M ≤
          Real.exp (-(1 / 10 : ℝ)) ^ segmentThreshold M :=
        pow_le_pow_left₀ (by norm_num) hbase _
      _ = Real.exp ((segmentThreshold M : ℝ) * (-(1 / 10 : ℝ))) :=
        (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-(12 * Real.log (M : ℝ))) :=
        Real.exp_monotone (by linarith)
  have hexp : Real.exp (-(12 * Real.log (M : ℝ))) = ((M : ℝ) ^ 12)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    have := Real.exp_nat_mul (Real.log (M : ℝ)) 12
    norm_num only [Nat.cast_ofNat] at this
    rw [this, Real.exp_log hMpos]
  rw [hexp] at htail
  have hmul := mul_le_mul_of_nonneg_right htail
    (show 0 ≤ (M : ℝ) ^ 12 by positivity)
  simpa [ne_of_gt hMpos] using hmul

/-- The segment-comparison count times the failure bound is below one. -/
theorem code_union_bound_lt_one {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 *
      (9 / 10 : ℝ) ^ segmentThreshold M < 1 := by
  have hx : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hpos : (0 : ℝ) < M := by linarith
  have hsq : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hpoly : (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 ≤ 8 * (M : ℝ) ^ 8 := by
    calc
      (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 ≤
          (M : ℝ) ^ 2 * (2 * (M : ℝ) ^ 2) ^ 3 := by
        gcongr
        linarith
      _ = 8 * (M : ℝ) ^ 8 := by ring
  have hfour : (8 : ℝ) < (M : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hx 4
    norm_num at h
    linarith
  have hpoly' : (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 < (M : ℝ) ^ 12 := by
    apply hpoly.trans_lt
    have h := mul_lt_mul_of_pos_right hfour (show (0 : ℝ) < (M : ℝ) ^ 8 by positivity)
    convert h using 1; ring
  have hmul := mul_lt_mul_of_pos_right hpoly'
    (show (0 : ℝ) < (9 / 10 : ℝ) ^ segmentThreshold M by positivity)
  exact hmul.trans_le (by simpa [mul_comm] using code_failure_power_bound (by omega : 1 ≤ M))

/-- One absolute threshold supplies both probabilistic and deterministic estimates. -/
theorem exists_code_numerical_threshold :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      2 ≤ M ∧
      2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2 ∧
      (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 *
        (9 / 10 : ℝ) ^ segmentThreshold M < 1 := by
  rcases exists_short_pair_threshold with ⟨M₀, hM₀⟩
  refine ⟨max M₀ 2, fun M hM => ?_⟩
  have hMtwo : 2 ≤ M := (le_max_right M₀ 2).trans hM
  exact ⟨hMtwo, (hM₀ M ((le_max_left M₀ 2).trans hM)).2,
    code_union_bound_lt_one hMtwo⟩

/-- Alphabet sizes below M only decrease the comparison count. -/
theorem code_union_bound_for_alphabet {K M : ℕ} (hK : K ≤ M) (hM : 2 ≤ M) :
    (K : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 *
      (9 / 10 : ℝ) ^ segmentThreshold M < 1 := by
  apply lt_of_le_of_lt _ (code_union_bound_lt_one hM)
  gcongr

/-- The short-pair threshold is no larger than the block width once its
error-absorption inequality holds. -/
theorem segmentThreshold_le_square {M : ℕ} (hM : 1 ≤ M)
    (h : 2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2) :
    segmentThreshold M ≤ M ^ 2 := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hnon : (0 : ℝ) ≤ segmentThreshold M := Nat.cast_nonneg _
  have h' : (segmentThreshold M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  exact_mod_cast h'

end TreeEdit.BinaryLower.Code

end OAI
