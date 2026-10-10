import OAI.Combinatorics.EditApproximation.Geometry.BandRegret
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Normalized increments of the actual child tables

The entropy hypotheses follow from monotonicity, bounds by the fixed child
mass, and spatial regularity. The table indices here start at zero, so the
gain at index `t` uses the table before update `t+1`.
-/

namespace EditApproximation

open Finset





theorem childDecrement_telescope {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (S : ℕ) (i : β × σ) :
    (∑ t ∈ range S, childDecrement mass table t i) =
      (table 0 i - table S i) / mass i.1 := by
  induction S with
  | zero => simp [childDecrement]
  | succ S ih =>
    rw [sum_range_succ, ih]
    unfold childDecrement
    ring

theorem childDecrement_nonneg {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (t : ℕ) (i : β × σ)
    (hmass : 0 < mass i.1) (hmono : table (t + 1) i ≤ table t i) :
    (0 : ℝ) ≤ childDecrement mass table t i := by
  exact_mod_cast div_nonneg (sub_nonneg.mpr hmono) hmass.le

theorem childDecrement_total_le {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (S : ℕ) (i : β × σ)
    (hmass : 0 < mass i.1) (hzero : 0 ≤ table S i) (hupper : table 0 i ≤ mass i.1) :
    (∑ t ∈ range S, (childDecrement mass table t i : ℝ)) ≤ 1 := by
  have htotal : (∑ t ∈ range S, childDecrement mass table t i) ≤ 1 := by
    rw [childDecrement_telescope]
    apply (div_le_one₀ hmass).2
    linarith
  exact_mod_cast htotal

theorem childGain_decrement_identity {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (κ : ℚ) (t : ℕ) (i : β × σ) :
    childGain mass table t i + (1 - κ) * childDecrement mass table t i =
      -(κ * table t i + (1 - κ) * table (t + 1) i) / mass i.1 := by
  unfold childGain childDecrement
  ring

theorem childGain_decrement_bounds {β σ : Type*} (mass : β → ℚ)
    (table : ℕ → β × σ → ℚ) (κ : ℚ) (t : ℕ) (i : β × σ)
    (hmass : 0 < mass i.1) (hκ : 0 ≤ κ) (hκone : κ ≤ 1)
    (hold : 0 ≤ table t i ∧ table t i ≤ mass i.1)
    (hnew : 0 ≤ table (t + 1) i ∧ table (t + 1) i ≤ mass i.1) :
    -1 ≤ (childGain mass table t i : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t i ∧
      (childGain mass table t i : ℝ) + (1 - (κ : ℝ)) * childDecrement mass table t i ≤ 0 := by
  have hweighted0 : 0 ≤ κ * table t i + (1 - κ) * table (t + 1) i :=
    add_nonneg (mul_nonneg hκ hold.1) (mul_nonneg (by linarith) hnew.1)
  have hweighted1 : κ * table t i + (1 - κ) * table (t + 1) i ≤ mass i.1 := by
    have ha := mul_le_mul_of_nonneg_left hold.2 hκ
    have hb := mul_le_mul_of_nonneg_left hnew.2 (by linarith : 0 ≤ 1 - κ)
    nlinarith
  have hbounds : -1 ≤ childGain mass table t i + (1 - κ) * childDecrement mass table t i ∧
      childGain mass table t i + (1 - κ) * childDecrement mass table t i ≤ 0 := by
    rw [childGain_decrement_identity]
    constructor
    · apply (le_div_iff₀ hmass).2
      linarith
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hweighted0) hmass.le
  constructor
  · exact_mod_cast hbounds.1
  · exact_mod_cast hbounds.2

theorem multiplicative_spatial_absolute {x y mass δ charge : ℝ}
    (hδ : 0 ≤ δ) (hx : x ≤ mass) (hy : y ≤ mass)
    (hxy : x ≤ (1 + δ) * y + charge) (hyx : y ≤ (1 + δ) * x + charge) :
    |x - y| ≤ δ * mass + charge := by
  have hxm := mul_le_mul_of_nonneg_left hx hδ
  have hym := mul_le_mul_of_nonneg_left hy hδ
  apply abs_le.mpr
  constructor <;> nlinarith

theorem normalized_decrement_range {old new old' new' mass δ spatial : ℝ}
    (hmass : 0 < mass)
    (hold : |old - old'| ≤ δ * mass + spatial)
    (hnew : |new - new'| ≤ δ * mass + spatial) :
    |(old - new) / mass - (old' - new') / mass| ≤ 2 * δ + 2 * spatial / mass := by
  have hid : (old - new) / mass - (old' - new') / mass =
      ((old - old') - (new - new')) / mass := by ring
  rw [hid, abs_div, abs_of_pos hmass]
  apply (div_le_iff₀ hmass).2
  have htriangle := (abs_sub _ _).trans (add_le_add hold hnew)
  have hcancel : (2 * δ + 2 * spatial / mass) * mass = 2 * δ * mass + 2 * spatial := by
    field_simp
  rw [hcancel]
  linarith

end EditApproximation

end OAI
