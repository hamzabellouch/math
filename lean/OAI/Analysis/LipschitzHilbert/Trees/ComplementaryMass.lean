import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! Relative motion of a mass fraction retains its complementary mass. -/

noncomputable section

namespace LipschitzHilbert

/-- The logarithm is Lipschitz on a positive half-line, with the sharp
reciprocal lower-bound constant. -/
theorem log_motion_of_lower_bound {x y c : ℝ} (hc : 0 < c)
    (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  have hdir (a b : ℝ) (ha : c ≤ a) (hb : c ≤ b) :
      Real.log a - Real.log b ≤ |a - b| / c := by
    have ha0 : 0 < a := hc.trans_le ha
    have hb0 : 0 < b := hc.trans_le hb
    calc
      Real.log a - Real.log b = Real.log (a / b) :=
        (Real.log_div ha0.ne' hb0.ne').symm
      _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
      _ ≤ |a - b| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hb
  apply abs_le.mpr
  constructor
  · have h := hdir y x hy hx
    rw [abs_sub_comm y x] at h
    linarith
  · exact hdir x y hx hy

/-- Two positive groups of mass moving relatively by at most `ε` have a
fraction error proportional to `r*(1-r)`, including a vanishing complement. -/
theorem complementary_mass_fraction_motion {A B A' B' ε : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hAmove : |A' - A| ≤ ε * A) (hBmove : |B' - B| ≤ ε * B) :
    0 < A' ∧ 0 < A' + B' ∧
      |A' / (A' + B') - A / (A + B)| ≤
        4 * ε * (A / (A + B)) * (1 - A / (A + B)) := by
  have hAlo : (1 - ε) * A ≤ A' := by linarith [(abs_le.mp hAmove).1]
  have hBlo : (1 - ε) * B ≤ B' := by linarith [(abs_le.mp hBmove).1]
  have hAp : 0 < A' := lt_of_lt_of_le (mul_pos (by linarith) hA) hAlo
  have hBp : 0 ≤ B' := (mul_nonneg (by linarith) hB).trans hBlo
  have hS : 0 < A + B := add_pos_of_pos_of_nonneg hA hB
  have hS' : 0 < A' + B' := add_pos_of_pos_of_nonneg hAp hBp
  have hslow : (A + B) / 2 ≤ A' + B' := by
    have hεA := mul_le_mul_of_nonneg_right hε1 hA.le
    have hεB := mul_le_mul_of_nonneg_right hε1 hB
    nlinarith
  have hnum : |(A' - A) * B - A * (B' - B)| ≤ 2 * ε * A * B := by
    calc
      _ ≤ |(A' - A) * B| + |A * (B' - B)| := abs_sub _ _
      _ = |A' - A| * B + A * |B' - B| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hB, abs_of_pos hA]
      _ ≤ (ε * A) * B + A * (ε * B) :=
        add_le_add (mul_le_mul_of_nonneg_right hAmove hB)
          (mul_le_mul_of_nonneg_left hBmove hA.le)
      _ = _ := by ring
  have hdiff : A' / (A' + B') - A / (A + B) =
      ((A' - A) * B - A * (B' - B)) / ((A' + B') * (A + B)) := by
    field_simp
    ring
  refine ⟨hAp, hS', ?_⟩
  rw [hdiff, abs_div, abs_of_pos (mul_pos hS' hS)]
  calc
    _ ≤ (2 * ε * A * B) / ((A' + B') * (A + B)) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg hS'.le hS.le)
    _ ≤ (2 * ε * A * B) / (((A + B) / 2) * (A + B)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hslow hS.le
    _ = _ := by
      field_simp
      ring

/-- The logarithmic fraction motion is proportional to the missing mass,
even if the complement vanishes. The constant is independent of the masses. -/
theorem complementary_mass_log_motion {A B A' B' ε : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hAmove : |A' - A| ≤ ε * A) (hBmove : |B' - B| ≤ ε * B) :
    |Real.log (A' / (A' + B')) - Real.log (A / (A + B))| ≤
      12 * ε * (1 - A / (A + B)) := by
  obtain ⟨hAp, hS', hmotion⟩ := complementary_mass_fraction_motion hA hB hε0 hε1 hAmove hBmove
  have hS : 0 < A + B := add_pos_of_pos_of_nonneg hA hB
  have hr : 0 < A / (A + B) := div_pos hA hS
  have hAlo : A / 2 ≤ A' := by
    have hmul := mul_le_mul_of_nonneg_right hε1 hA.le
    linarith [(abs_le.mp hAmove).1]
  have hShi : A' + B' ≤ (3 / 2) * (A + B) := by
    have hmulA := mul_le_mul_of_nonneg_right hε1 hA.le
    have hmulB := mul_le_mul_of_nonneg_right hε1 hB
    linarith [(abs_le.mp hAmove).2, (abs_le.mp hBmove).2]
  have hrlo : (A / (A + B)) / 3 ≤ A' / (A' + B') := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hS (by norm_num)) hS').2
    have h1 := mul_le_mul_of_nonneg_left hShi hA.le
    have h2 := mul_le_mul_of_nonneg_right hAlo hS.le
    nlinarith
  calc
    _ ≤ |A' / (A' + B') - A / (A + B)| / ((A / (A + B)) / 3) :=
      log_motion_of_lower_bound (div_pos hr (by norm_num)) hrlo (by linarith)
    _ ≤ (4 * ε * (A / (A + B)) * (1 - A / (A + B))) /
        ((A / (A + B)) / 3) := div_le_div_of_nonneg_right hmotion (by positivity)
    _ = _ := by field_simp; ring

end LipschitzHilbert

end

end OAI
