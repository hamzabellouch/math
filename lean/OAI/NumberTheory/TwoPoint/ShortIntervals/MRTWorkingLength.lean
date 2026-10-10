import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcSubdivision
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Cap the original short length before choosing its prime bands. The
uncapped branch is kept exactly; on the capped branch the omitted final
block is negligible compared with W^(-1/4). -/

namespace TwoPointCorrelations

open Filter

noncomputable def mrtWorkingCap (W : ℝ) : ℕ :=
  ⌊Real.exp (Real.sqrt W / 2)⌋₊

noncomputable def mrtWorkingLength (H : ℕ) (W : ℝ) : ℕ :=
  if (H : ℝ) ≤ Real.exp (Real.sqrt W) then H else mrtWorkingCap W

lemma mrt_working_cap_upper (W : ℝ) :
    (mrtWorkingCap W : ℝ) ≤ Real.exp (Real.sqrt W / 2) :=
  Nat.floor_le (Real.exp_pos _).le

/-- The fixed cap eventually exceeds every prescribed power of W. -/
theorem mrt_working_cap_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, W ^ a ≤ (mrtWorkingCap W : ℝ) := by
  have hsmall := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hlarge := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually
    (eventually_ge_atTop (8 * ((a : ℝ) + 1)))
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℝ)] with W hs ht hW
  have hW0 : 0 < W := by linarith
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW
  have ht0 : 0 ≤ W ^ (1 / 4 : ℝ) := Real.rpow_nonneg hW0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_nonneg ht0, one_mul] at hs
  have ht2 : (W ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt W := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, Real.sqrt_eq_rpow]
    norm_num
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have ham := mul_le_mul_of_nonneg_left hs ha
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hmul := mul_nonneg ht0 (sub_nonneg.mpr ht)
  have he : Real.log 2 + (a : ℝ) * Real.log W ≤ Real.sqrt W / 2 := by
    nlinarith
  have hpow : 2 * W ^ a ≤ Real.exp (Real.sqrt W / 2) := by
    calc
      _ = Real.exp (Real.log 2 + (a : ℝ) * Real.log W) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          Real.exp_nat_mul, Real.exp_log hW0]
      _ ≤ _ := Real.exp_le_exp.mpr he
  have hp : 1 ≤ W ^ a := one_le_pow₀ hW
  have hf := Nat.lt_floor_add_one (Real.exp (Real.sqrt W / 2))
  change Real.exp (Real.sqrt W / 2) < (mrtWorkingCap W : ℝ) + 1 at hf
  linarith

lemma mrt_working_length_upper {H : ℕ} {W : ℝ} :
    mrtWorkingLength H W ≤ H := by
  unfold mrtWorkingLength
  split_ifs with h
  · exact le_rfl
  · have hh : (mrtWorkingCap W : ℝ) ≤ H :=
      (mrt_working_cap_upper W).trans
        ((Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg W])).trans (le_of_not_ge h))
    exact_mod_cast hh

lemma mrt_working_length_exp_upper (H : ℕ) (W : ℝ) :
    (mrtWorkingLength H W : ℝ) ≤ Real.exp (Real.sqrt W) := by
  unfold mrtWorkingLength
  split_ifs with h
  · exact h
  · exact (mrt_working_cap_upper W).trans
      (Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg W]))

lemma mrt_working_length_power {H a : ℕ} {W : ℝ}
    (hH : W ^ a ≤ (H : ℝ)) (hcap : W ^ a ≤ (mrtWorkingCap W : ℝ)) :
    W ^ a ≤ (mrtWorkingLength H W : ℝ) := by
  unfold mrtWorkingLength
  split_ifs <;> assumption

lemma mrt_working_tail_exp {W : ℝ} (hW : 0 < W) :
    Real.exp (-Real.sqrt W / 2) ≤ W ^ (-(1 / 4 : ℝ)) := by
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hlog := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hW.le] at hlog
  rw [Real.rpow_def_of_pos hW]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Either no subdivision is performed, or the final incomplete block
has relative length at most W^(-1/4). -/
lemma mrt_working_length_remainder {H : ℕ} {W : ℝ} (hW : 0 < W) :
    mrtWorkingLength H W = H ∨
      (mrtWorkingLength H W : ℝ) / H ≤ W ^ (-(1 / 4 : ℝ)) := by
  unfold mrtWorkingLength
  split_ifs with h
  · exact Or.inl rfl
  · right
    have hH : Real.exp (Real.sqrt W) ≤ (H : ℝ) := le_of_not_ge h
    have hH0 : (0 : ℝ) < H := (Real.exp_pos _).trans_le hH
    calc
      (mrtWorkingCap W : ℝ) / H ≤ Real.exp (Real.sqrt W / 2) / H :=
        div_le_div_of_nonneg_right (mrt_working_cap_upper W) hH0.le
      _ ≤ Real.exp (Real.sqrt W / 2) / Real.exp (Real.sqrt W) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hH
      _ = Real.exp (-Real.sqrt W / 2) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      _ ≤ _ := mrt_working_tail_exp hW

lemma mrt_working_length_loglog {H : ℕ} {W : ℝ}
    (hW : 0 < W) (hH : (1 : ℝ) < mrtWorkingLength H W) :
    Real.log (Real.log (mrtWorkingLength H W : ℝ)) ≤ (1 / 2 : ℝ) * Real.log W := by
  have hpos : (0 : ℝ) < mrtWorkingLength H W := by linarith
  have hlpos := Real.log_pos hH
  have hlog := Real.log_le_log hpos (mrt_working_length_exp_upper H W)
  rw [Real.log_exp] at hlog
  have hh := Real.log_le_log hlpos hlog
  rw [Real.log_sqrt hW.le] at hh
  linarith

theorem mrt_working_cap_log :
    ∀ᶠ W : ℝ in atTop, Real.sqrt W / 4 ≤ Real.log (mrtWorkingCap W : ℝ) := by
  have hs := Real.tendsto_sqrt_atTop.eventually
    (eventually_ge_atTop (max (4 * Real.log 2) (2 * Real.log 2)))
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with W hs hW
  have hroot : 4 * Real.log 2 ≤ Real.sqrt W := (le_max_left _ _).trans hs
  have hroot' : 2 * Real.log 2 ≤ Real.sqrt W := (le_max_right _ _).trans hs
  have hexp : (2 : ℝ) ≤ Real.exp (Real.sqrt W / 2) := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hfloor := Nat.lt_floor_add_one (Real.exp (Real.sqrt W / 2))
  change Real.exp (Real.sqrt W / 2) < (mrtWorkingCap W : ℝ) + 1 at hfloor
  have hlo : Real.exp (Real.sqrt W / 2) / 2 ≤ (mrtWorkingCap W : ℝ) := by linarith
  have hh := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num)) hlo
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] at hh
  linarith

/-- The bound W ≤ log(H)^5 forces H above any fixed power of W. -/
theorem mrt_working_original_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℝ, 0 < H → 1 ≤ Real.log H →
      W ≤ (Real.log H) ^ (5 : ℕ) → W ^ a ≤ H := by
  have hs := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have ht := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually
    (eventually_ge_atTop (a : ℝ))
  filter_upwards [hs, ht, eventually_ge_atTop (1 : ℝ)] with W hs ht hW
  have hW0 : 0 < W := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hW), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hW0.le _), one_mul] at hs
  intro H hH0 hlog hWH
  have hp : W ^ (1 / 5 : ℝ) ≤ Real.log H := by
    calc
      _ ≤ ((Real.log H) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow hW0.le hWH (by norm_num)
      _ = Real.log H := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Real.log H)]
        norm_num
  have ha : (a : ℝ) * Real.log W ≤ W ^ (1 / 5 : ℝ) := by
    calc
      _ ≤ W ^ (1 / 10 : ℝ) * W ^ (1 / 10 : ℝ) :=
        mul_le_mul ht hs (Real.log_nonneg hW) (Real.rpow_nonneg hW0.le _)
      _ = _ := by rw [← Real.rpow_add hW0]; norm_num
  calc
    W ^ a = Real.exp ((a : ℝ) * Real.log W) := by
      rw [Real.exp_nat_mul, Real.exp_log hW0]
    _ ≤ Real.exp (Real.log H) := Real.exp_le_exp.mpr (ha.trans hp)
    _ = H := Real.exp_log hH0

end TwoPointCorrelations

end OAI
