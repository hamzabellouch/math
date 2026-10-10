import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterMomentBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

def gridMomentParameter (T : ℝ) : ℕ := ⌊T ^ (1 / 1000000 : ℝ)⌋₊

theorem eventually_auxiliaryK_lower (a : ℝ) (ha : 0 ≤ a) (hag : a + auxiliaryExponent < 1) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      1 ≤ z → T ^ auxiliaryExponent / 2 ≤ Real.log z →
      Real.log z ≤ 2 * T ^ auxiliaryExponent → T ^ a ≤ (auxiliaryK Z z : ℝ) := by
  filter_upwards [eventually_auxiliary_size_conditions,
    eventually_mul_rpow_le_rpow 600 hag] with T hc hg
  intro Z z hZl hZu hz hzl hzu
  have hT : 0 < T := by linarith [hc.1]
  have hy : 0 < T ^ auxiliaryExponent := Real.rpow_pos_of_pos hT _
  have hb := auxiliaryK_mul_bounds hT.le hy (by linarith [hc.2.2.1]) hZl hZu hz hzl hzu
  have hp : T ^ auxiliaryExponent * T ^ a = T ^ (a + auxiliaryExponent) := by
    rw [← Real.rpow_add hT]
    congr 1
    ring
  have hp1 : 1 ≤ T ^ a := Real.one_le_rpow hc.1 ha
  rw [Real.rpow_one, ← hp] at hg
  nlinarith [hb.1]

theorem eventually_auxiliaryK_le_log (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      1 ≤ z → T ^ auxiliaryExponent / 2 ≤ Real.log z →
      Real.log z ≤ 2 * T ^ auxiliaryExponent → (auxiliaryK Z z : ℝ) ≤ ε * Real.log Z := by
  have hs := (isLittleO_rpow_of_lt (show 1 - auxiliaryExponent < 1 by
    linarith [auxiliaryExponent_pos])).bound (half_pos hε)
  filter_upwards [eventually_auxiliaryK_bounds, eventually_ge_atTop (0 : ℝ), hs] with T hK hT hs
  intro Z z hZl hZu hz hzl hzu
  simp only [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hT,
    abs_of_nonneg (Real.rpow_nonneg hT _)] at hs
  have hupper := (hK Z z hZl hZu hz hzl hzu).2
  have hm := mul_le_mul_of_nonneg_left hZl hε.le
  linarith

theorem eventually_grid_cost_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      1 ≤ z → T ^ auxiliaryExponent / 2 ≤ Real.log z →
      Real.log z ≤ 2 * T ^ auxiliaryExponent →
      Real.log Z / (gridMomentParameter T : ℝ) ≤ ε * auxiliaryK Z z := by
  have hK := eventually_auxiliaryK_lower (1 - 2 * auxiliaryExponent)
    (by norm_num [auxiliaryExponent]) (by norm_num [auxiliaryExponent])
  have hs := ((isLittleO_rpow_of_lt
    (show (1 - 1 / 1000000 : ℝ) < 1 - 2 * auxiliaryExponent by norm_num [auxiliaryExponent])).const_mul_left 4).bound hε
  filter_upwards [hK, hs, eventually_gt_atTop (0 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000000)).eventually_ge_atTop 2]
    with T hK hs hT hp
  intro Z z hZl hZu hz hzl hzu
  have hf := Nat.lt_floor_add_one (T ^ (1 / 1000000 : ℝ))
  have hhalf : T ^ (1 / 1000000 : ℝ) / 2 ≤ (gridMomentParameter T : ℝ) := by
    unfold gridMomentParameter
    linarith
  have hl : (0 : ℝ) < gridMomentParameter T := by linarith
  have hpow : 0 < T ^ (1 - 1 / 1000000 : ℝ) := Real.rpow_pos_of_pos hT _
  have hid : T ^ (1 / 1000000 : ℝ) * T ^ (1 - 1 / 1000000 : ℝ) = T := by
    rw [← Real.rpow_add hT]
    norm_num
  have hratio : Real.log Z / (gridMomentParameter T : ℝ) ≤
      4 * T ^ (1 - 1 / 1000000 : ℝ) := by
    apply (div_le_iff₀ hl).mpr
    have hm := mul_le_mul_of_nonneg_right hhalf hpow.le
    nlinarith
  have hsmall : 4 * T ^ (1 - 1 / 1000000 : ℝ) ≤ ε * T ^ (1 - 2 * auxiliaryExponent) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hT.le _),
      abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg hT.le _))] using hs
  exact hratio.trans (hsmall.trans (mul_le_mul_of_nonneg_left (hK Z z hZl hZu hz hzl hzu) hε.le))

theorem eventually_moment_mul_log_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      1 ≤ z → T ^ auxiliaryExponent / 2 ≤ Real.log z →
      Real.log z ≤ 2 * T ^ auxiliaryExponent →
      (evenMomentParameter (parameterX T) Z : ℝ) * Real.log T ≤ ε * auxiliaryK Z z := by
  have hs := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 20)).bound
    (div_pos hε (by norm_num : (0 : ℝ) < 14))
  filter_upwards [eventually_evenMomentParameter_bound, eventually_auxiliaryK_bounds,
    eventually_ge_atTop (1 : ℝ), hs] with T hk hK hT hs
  intro Z z hZl hZu hz hzl hzu
  have ht : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (Real.rpow_nonneg ht.le _)] at hs
  have hm := mul_le_mul (hk Z hZl) hs hlog
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 14) (Real.rpow_nonneg ht.le _))
  have hid : (14 * T ^ (3 / 5 : ℝ)) * (ε / 14 * T ^ (3 / 20 : ℝ)) =
      ε * T ^ (3 / 4 : ℝ) := by
    rw [show (3 / 4 : ℝ) = 3 / 5 + 3 / 20 by norm_num, Real.rpow_add ht]
    ring
  rw [hid] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (hK Z z hZl hZu hz hzl hzu).1 hε.le)

end Ostmann.QuadraticCenter

end

end OAI
