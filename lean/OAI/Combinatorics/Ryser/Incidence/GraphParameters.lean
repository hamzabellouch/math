import OAI.Combinatorics.Ryser.Incidence.Parameters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem graphScale_bounds {U : ℝ} (hU : 2 ≤ U) :
    2 ≤ graphScale U ∧ 16 * U ^ 3 ≤ graphScale U := by
  have hU1 : 1 ≤ U := le_trans (by norm_num) hU
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hC : 16 ≤ graphScaleConstant := by norm_num [graphScaleConstant]
  have hpow : 1 ≤ U ^ 39 := one_le_pow₀ hU1
  constructor
  · calc
      2 ≤ graphScaleConstant := le_trans (by norm_num) hC
      _ ≤ graphScaleConstant * U ^ 39 :=
        le_mul_of_one_le_right graphScaleConstant_pos.le hpow
      _ = graphScale U := rfl
  · calc
      16 * U ^ 3 ≤ graphScaleConstant * U ^ 3 :=
        mul_le_mul_of_nonneg_right hC (pow_nonneg hU0 _)
      _ ≤ graphScaleConstant * U ^ 39 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU1 (by decide))
          graphScaleConstant_pos.le
      _ = graphScale U := rfl

theorem two_le_expansionScale {V : ℝ} (hV : 2 ≤ V) : 2 ≤ expansionScale V := by
  have hV1 : 1 ≤ V := le_trans (by norm_num) hV
  calc
    2 ≤ (2 : ℝ) ^ 23 := by norm_num
    _ ≤ 2 ^ 23 * V ^ 24 :=
      le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hV1)
    _ = expansionScale V := rfl

theorem retained_witness_lower (r U w g : ℝ) (hr : 0 < r) (hU : 2 ≤ U)
    (hW : r ^ 2 / (9 * 2 ^ 57 * U ^ 39) ≤ w)
    (hG : w - 3 * (16 * U ^ 3 * r) ≤ g)
    (hremove : (96 / witnessConstant) * U ^ 42 ≤ r) :
    r ^ 2 / graphScale U ≤ g := by
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hVpos := graphScale_pos hUpos
  have hloss : 3 * (16 * U ^ 3 * r) ≤ r ^ 2 / graphScale U := by
    apply (le_div_iff₀ hVpos).mpr
    calc
      3 * (16 * U ^ 3 * r) * graphScale U =
          ((96 / witnessConstant) * U ^ 42) * r := by
        norm_num [graphScale, graphScaleConstant, witnessConstant]
        ring
      _ ≤ r * r := mul_le_mul_of_nonneg_right hremove hr.le
      _ = r ^ 2 := (pow_two r).symm
  have htwice : 2 * (r ^ 2 / graphScale U) ≤ w := by
    convert hW using 1
    dsimp [graphScale, graphScaleConstant]
    field_simp [ne_of_gt hUpos]

  linarith

theorem extraction_expansion_le (r V s : ℝ) (hr : 0 ≤ r) (hV : 0 < V)
    (hlo : 3 * r / (8 * V ^ 2) ≤ s) :
    2 ^ 20 * V ^ 22 * r ≤ expansionScale V * s := by
  have hB : 0 ≤ (2 : ℝ) ^ 20 * V ^ 22 * r := by positivity
  calc
    2 ^ 20 * V ^ 22 * r ≤ 3 * (2 ^ 20 * V ^ 22 * r) := by linarith
    _ = expansionScale V * (3 * r / (8 * V ^ 2)) := by
      dsimp [expansionScale]
      field_simp [ne_of_gt hV]
      norm_num
      ring
    _ ≤ expansionScale V * s :=
      mul_le_mul_of_nonneg_left hlo (expansionScale_pos hV).le

end RyserCoveringCounterexample.Incidence

end OAI
