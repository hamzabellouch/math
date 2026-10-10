import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OAI

namespace RyserCoveringCounterexample.Incidence

noncomputable def upperDegreeCutoff (U q : ℝ) : ℝ := 16 * U ^ 3 * Real.sqrt q

noncomputable def lowerDegreeCutoff (U q : ℝ) : ℝ := Real.sqrt q / (8 * U ^ 2)

theorem upperDegreeCutoff_pos {U q : ℝ} (hU : 0 < U) (hq : 0 < q) :
    0 < upperDegreeCutoff U q :=
  mul_pos (mul_pos (by norm_num) (pow_pos hU _)) (Real.sqrt_pos.mpr hq)

theorem lowerDegreeCutoff_pos {U q : ℝ} (hU : 0 < U) (hq : 0 < q) :
    0 < lowerDegreeCutoff U q :=
  div_pos (Real.sqrt_pos.mpr hq) (mul_pos (by norm_num) (pow_pos hU _))

private theorem pruning_budget_identity (U q t : ℝ) (hU : U ≠ 0) (ht : t ≠ 0)
    (hsq : t ^ 2 = q) :
    q * t / U - (2 * U ^ 2 * q ^ 2) / (16 * U ^ 3 * t) -
      (2 * U ^ 2 * q ^ 2) / (16 * U ^ 3 * t) -
      (t / (8 * U ^ 2)) * (2 * U * q) = q * t / (2 * U) := by
  rw [← hsq]
  field_simp [hU, ht]
  ring

theorem pruning_budget_exact {U q : ℝ} (hU : 0 < U) (hq : 0 < q) :
    q * Real.sqrt q / U - (2 * U ^ 2 * q ^ 2) / upperDegreeCutoff U q -
      (2 * U ^ 2 * q ^ 2) / upperDegreeCutoff U q -
      lowerDegreeCutoff U q * (2 * U * q) = q * Real.sqrt q / (2 * U) := by
  exact pruning_budget_identity U q (Real.sqrt q) hU.ne'
    (Real.sqrt_pos.mpr hq).ne' (Real.sq_sqrt hq.le)

theorem pruned_card_ratio {U q : ℝ} (hU : 0 < U) (hq : 0 < q) :
    (q * Real.sqrt q / (2 * U)) / upperDegreeCutoff U q = q / (32 * U ^ 4) := by
  have ht := (Real.sqrt_pos.mpr hq).ne'
  have hU' := hU.ne'
  unfold upperDegreeCutoff
  field_simp [hU', ht]
  ring

theorem cutoff_product {U q : ℝ} (hU : 0 < U) (hq : 0 ≤ q) :
    upperDegreeCutoff U q * lowerDegreeCutoff U q = 2 * U * q := by
  have hU' := hU.ne'
  unfold upperDegreeCutoff lowerDegreeCutoff
  calc
    16 * U ^ 3 * Real.sqrt q * (Real.sqrt q / (8 * U ^ 2)) =
        2 * U * (Real.sqrt q) ^ 2 := by
      field_simp [hU']
      ring
    _ = 2 * U * q := by rw [Real.sq_sqrt hq]

theorem all_line_cap_numeric {U q n : ℝ} (hU : 0 < U) (hq : 0 < q)
    (hd : 2 ≤ lowerDegreeCutoff U q) (hn : n ≤ U * q) :
    n / (lowerDegreeCutoff U q - 1) ≤ upperDegreeCutoff U q := by
  have hH := upperDegreeCutoff_pos hU hq
  have hproduct := cutoff_product hU hq.le
  have hhalf : upperDegreeCutoff U q ≤ U * q := by nlinarith
  apply (div_le_iff₀ (show 0 < lowerDegreeCutoff U q - 1 by linarith)).2
  nlinarith

end RyserCoveringCounterexample.Incidence

end OAI
