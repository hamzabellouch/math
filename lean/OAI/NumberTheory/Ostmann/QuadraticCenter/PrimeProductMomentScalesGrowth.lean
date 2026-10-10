import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterCostBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_primeProduct_moment_orders :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ gridMomentParameter T ∧
      4096*gridMomentParameter T ≤ evenMomentParameter (parameterX T) Z ∧
      (evenMomentParameter (parameterX T) Z : ℝ) ≤ T := by
  filter_upwards [eventually_parameterX_log_bounds,eventually_evenMomentParameter_bound,
    eventually_mul_rpow_le_rpow 16384 (a := 1/1000000) (b := 3/5) (by norm_num),
    eventually_mul_rpow_le_rpow 14 (a := 3/5) (b := 1) (by norm_num),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/1000000)).eventually_ge_atTop 2]
    with T hX hk hgap hupper hlower
  intro Z hZl hZu
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hX.1
  have hlogZ : 0 < Real.log Z := (half_pos hT).trans_le hZl
  have hlogX : 0 ≤ Real.log (parameterX T : ℝ) := by linarith [hX.2.1]
  have hord := (evenMomentParameter_bounds (parameterX T) Z
    (show 0 ≤ Real.log (parameterX T : ℝ)/Real.log Z+10 by positivity)).1
  have hratio : Real.log (parameterX T : ℝ)/Real.log Z ≤
      (evenMomentParameter (parameterX T) Z : ℝ) := by linarith
  have hmul := (div_le_iff₀ hlogZ).mp hratio
  have hmul' := mul_le_mul_of_nonneg_left hZu
    (Nat.cast_nonneg (evenMomentParameter (parameterX T) Z) : (0 : ℝ) ≤ _)
  have hid : T*T^(3/5 : ℝ) = T^(8/5 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one T]
    rw [← Real.rpow_add hT]
    norm_num
  have hlow : T^(3/5 : ℝ)/4 ≤ (evenMomentParameter (parameterX T) Z : ℝ) := by
    apply (mul_le_mul_iff_right₀ hT).mp
    rw [← mul_div_assoc,hid]
    nlinarith [hX.2.2.1]
  have hfloor : (gridMomentParameter T : ℝ) ≤ T^(1/1000000 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hT.le _)
  have hl : 1 ≤ gridMomentParameter T := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.floor_pos.mpr (show 1 ≤ T^(1/1000000 : ℝ) by linarith)))
  have hkl : (4096 : ℝ)*gridMomentParameter T ≤ evenMomentParameter (parameterX T) Z := by
    nlinarith [hfloor,hgap,hlow]
  refine ⟨hl,by exact_mod_cast hkl,?_⟩
  exact (hk Z hZl).trans (by simpa only [Real.rpow_one] using hupper)

theorem eventually_primeProduct_probability_scale (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      2 ≤ T ∧ 8/c ≤ T ∧ 1 ≤ Real.log Z ∧ (2 : ℝ) ≤ Z ∧
      2*(evenMomentParameter (parameterX T) Z : ℝ)*Real.log Z/c ≤ Real.sqrt (Z : ℝ) ∧
      ∀ J : ℕ, c*(Z : ℝ)/Real.log Z ≤ J →
        0 < J ∧ 2*evenMomentParameter (parameterX T) Z ≤ J := by
  have hg := (isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0 : ℝ)<1/4)).bound
    (div_pos hc (by norm_num : (0 : ℝ)<4))
  filter_upwards [eventually_primeProduct_moment_orders,hg,eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (8/c)] with T horders hg hT hcT
  intro Z hZl hZu
  have hTp : 0 < T := by linarith
  have hlogZ : 1 ≤ Real.log Z := by linarith
  have hZpos : 0 < (Z : ℝ) := by
    have hh := (Real.log_pos_iff (Nat.cast_nonneg Z)).mp (show 0 < Real.log Z by linarith)
    linarith
  have hZ2 : (2 : ℝ) ≤ Z := by
    have hh := Real.add_one_le_exp (Real.log (Z : ℝ))
    rw [Real.exp_log hZpos] at hh
    linarith
  have hrootsq : Real.sqrt (Z : ℝ) = Real.exp (Real.log (Z : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hZpos]
    congr 1
    ring
  have hroot : Real.exp ((1/4 : ℝ)*T) ≤ Real.sqrt (Z : ℝ) := by
    rw [hrootsq]
    apply Real.exp_le_exp.mpr
    linarith
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg T),
    abs_of_pos (Real.exp_pos _)] at hg
  have hk := (horders Z hZl hZu).2.2
  have hscale : 2*(evenMomentParameter (parameterX T) Z : ℝ)*Real.log Z/c ≤
      Real.sqrt (Z : ℝ) := by
    apply (div_le_iff₀ hc).mpr
    have hm := mul_le_mul hk hZu (show 0 ≤ Real.log Z by linarith) hTp.le
    have he := mul_le_mul_of_nonneg_left hroot hc.le
    nlinarith
  refine ⟨hT,hcT,hlogZ,hZ2,hscale,?_⟩
  intro J hJ
  have hJpos : (0 : ℝ) < J :=
    (div_pos (mul_pos hc hZpos) (by linarith)).trans_le hJ
  have hrootZ : Real.sqrt (Z : ℝ) ≤ Z := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hscale' := (div_le_iff₀ hc).mp (hscale.trans hrootZ)
  have horder : 2*(evenMomentParameter (parameterX T) Z : ℝ) ≤ c*(Z : ℝ)/Real.log Z := by
    apply (le_div_iff₀ (show 0 < Real.log Z by linarith)).mpr
    nlinarith
  exact ⟨by exact_mod_cast hJpos,by exact_mod_cast horder.trans hJ⟩

end Ostmann.QuadraticCenter

end

end OAI
