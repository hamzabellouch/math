import OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingLength
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcOuterScale

namespace OAI

/-! The capped working length fits below the common square-root origin
cutoff. Its boundary remains negligible after the correction division. -/

namespace TwoPointCorrelations

open Filter

theorem mrt_working_length_add_two_below_sqrt :
    ∀ᶠ X : ℕ in atTop, ∀ W : ℝ, 1 ≤ W →
      W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ H : ℕ, majorArcWorkingLength H W+2 ≤ ⌈Real.sqrt (X:ℝ)⌉₊ := by
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<624/625 by norm_num)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [hlog.eventually hp,hlog.eventually (eventually_ge_atTop (4:ℝ)),
    eventually_ge_atTop (2:ℕ)] with X hp hL hX
  change 4 ≤ (Real.log (X:ℝ))^(624/625:ℝ) at hp
  intro W hW hWX H
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hL0 : 0 < Real.log (X:ℝ) := by linarith
  have hpow : (Real.log (X:ℝ))^(1/625:ℝ) ≤ Real.log (X:ℝ)/4 := by
    have he : (Real.log (X:ℝ))^(1/625:ℝ)*
        (Real.log (X:ℝ))^(624/625:ℝ)=Real.log (X:ℝ) := by
      rw [← Real.rpow_add hL0]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hp
      (Real.rpow_nonneg hL0.le (1/625))
    rw [he] at hh
    linarith
  have hroot : W^(1/5:ℝ) ≤ Real.log (X:ℝ)/4 := by
    calc
      _ ≤ ((Real.log (X:ℝ))^(1/125:ℝ))^(1/5:ℝ) :=
        Real.rpow_le_rpow (by linarith) hWX (by norm_num)
      _ = (Real.log (X:ℝ))^(1/625:ℝ) := by
        rw [← Real.rpow_mul hL0.le]
        norm_num
      _ ≤ _ := hpow
  have hsize : (majorArcWorkingLength H W:ℝ) ≤ Real.exp (Real.log (X:ℝ)/4) :=
    (major_arc_working_length_exp_upper H (by linarith)).trans (Real.exp_le_exp.mpr hroot)
  have he : (Real.exp (Real.log (X:ℝ)/4))^2=Real.sqrt (X:ℝ) := by
    rw [pow_two,← Real.exp_add,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hX0]
    congr 1
    ring
  have htwo : 2 ≤ Real.exp (Real.log (X:ℝ)/4) := by
    linarith [Real.add_one_le_exp (Real.log (X:ℝ)/4)]
  have hsum : (majorArcWorkingLength H W:ℝ)+2 ≤ Real.sqrt (X:ℝ) := by
    nlinarith
  have hh := hsum.trans (Nat.le_ceil (Real.sqrt (X:ℝ)))
  exact_mod_cast hh

theorem mrt_working_length_below_sqrt :
    ∀ᶠ X : ℕ in atTop, ∀ W : ℝ, 1 ≤ W →
      W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ H : ℕ, majorArcWorkingLength H W+1 ≤ ⌈Real.sqrt (X:ℝ)⌉₊ := by
  filter_upwards [mrt_working_length_add_two_below_sqrt] with X hX
  intro W hW hWX H
  exact (show majorArcWorkingLength H W+1 ≤ majorArcWorkingLength H W+2 by omega).trans
    (hX W hW hWX H)

theorem mrt_working_quotient_boundary :
    ∀ᶠ X : ℕ in atTop, ∀ W : ℝ, 1 ≤ W →
      W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ d : ℕ, 0 < d → (d:ℝ) ≤ W^5 →
      ((2*⌈Real.sqrt (X:ℝ)⌉₊+1:ℕ):ℝ)/(X/d+1:ℕ) ≤ (W^4)⁻¹ := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/2 by norm_num)).bound
    (show (0:ℝ)<1/5 by norm_num)
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hb,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop (2:ℕ)]
    with X hb hL hX
  intro W hW hWX d hd hdW
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hL0 : 0 < Real.log (X:ℝ) := by linarith
  have hW0 : 0 < W := by linarith
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤X by omega))),
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hX0.le _)] at hb
  have hfive : 5*Real.log (X:ℝ) ≤ Real.sqrt (X:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    linarith
  have hs1 : 1 ≤ Real.sqrt (X:ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1≤X by omega))
  have hceil : (⌈Real.sqrt (X:ℝ)⌉₊:ℝ) ≤ 2*Real.sqrt (X:ℝ) := by
    have hh := Nat.ceil_lt_add_one (Real.sqrt_nonneg (X:ℝ))
    linarith
  have hnum : ((2*⌈Real.sqrt (X:ℝ)⌉₊+1:ℕ):ℝ) ≤ 5*Real.sqrt (X:ℝ) := by
    push_cast
    linarith
  have hW9 : W^9 ≤ Real.log (X:ℝ) := by
    calc
      _ ≤ ((Real.log (X:ℝ))^(1/125:ℝ))^9 :=
        pow_le_pow_left₀ hW0.le hWX 9
      _ = (Real.log (X:ℝ))^(9/125:ℝ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
        norm_num
      _ ≤ _ := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          hL (show (9/125:ℝ)≤1 by norm_num)
  have hd4 : (d:ℝ)*W^4 ≤ Real.log (X:ℝ) := by
    calc
      _ ≤ W^5*W^4 := mul_le_mul_of_nonneg_right hdW (pow_nonneg hW0.le _)
      _ = W^9 := by ring
      _ ≤ _ := hW9
  have hprod : ((2*⌈Real.sqrt (X:ℝ)⌉₊+1:ℕ):ℝ)*W^4*(d:ℝ) ≤ X := by
    calc
      _ ≤ (5*Real.sqrt (X:ℝ))*W^4*(d:ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnum (pow_nonneg hW0.le _)) hd0.le
      _ = (5*Real.sqrt (X:ℝ))*((d:ℝ)*W^4) := by ring
      _ ≤ (5*Real.sqrt (X:ℝ))*Real.log (X:ℝ) :=
        mul_le_mul_of_nonneg_left hd4 (by positivity)
      _ ≤ (Real.sqrt (X:ℝ))^2 := by nlinarith [Real.sqrt_nonneg (X:ℝ)]
      _ = _ := Real.sq_sqrt hX0.le
  have hquot : (X:ℝ)/d < (X/d+1:ℕ) := by
    apply (div_lt_iff₀ hd0).mpr
    have hh : (X:ℝ) < (d:ℝ)*(X/d+1:ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ X hd
    simpa only [mul_comm] using hh
  have hmul : ((2*⌈Real.sqrt (X:ℝ)⌉₊+1:ℕ):ℝ)*W^4 ≤ (X/d+1:ℕ) :=
    ((le_div_iff₀ hd0).mpr hprod).trans hquot.le
  have hden : (0:ℝ) < (X/d+1:ℕ) := by positivity
  calc
    _ ≤ (((X/d+1:ℕ):ℝ)/W^4)/(X/d+1:ℕ) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ (pow_pos hW0 4)).mpr hmul) hden.le
    _ = _ := by field_simp [hden.ne',hW0.ne']

end TwoPointCorrelations

end OAI
