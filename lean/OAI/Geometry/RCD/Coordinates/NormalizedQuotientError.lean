import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Normalizing a bounded test by a convergent positive mass -/

namespace RegularPointCoordinates

theorem normalized_quotient_error {a ak b bk : ℝ} (hb : 0<b) (hbk : b/2≤bk) (ha : |a|≤b) :
    |ak/bk-a/b|≤(2/b)*(|ak-a|+|bk-b|) := by
  have hbk0 : 0<bk := (half_pos hb).trans_le hbk
  have he : ak/bk-a/b=((ak-a)+(a/b)*(b-bk))/bk := by
    field_simp
    ring
  have hab : |a/b|≤1 := by
    rw [abs_div,abs_of_pos hb]
    exact (div_le_one hb).mpr ha
  have hn : |(ak-a)+(a/b)*(b-bk)|≤|ak-a|+|bk-b| := by
    calc _ ≤ |ak-a|+|(a/b)*(b-bk)| := abs_add_le _ _
         _ = |ak-a|+|a/b| * |bk-b| := by rw [abs_mul,abs_sub_comm b bk]
         _ ≤ |ak-a|+|bk-b| := add_le_add le_rfl (mul_le_of_le_one_left (abs_nonneg _) hab)
  rw [he,abs_div,abs_of_pos hbk0]
  calc _ ≤ (|ak-a|+|bk-b|)/bk := div_le_div_of_nonneg_right hn hbk0.le
       _ ≤ (|ak-a|+|bk-b|)/(b/2) :=
         div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _)) (half_pos hb) hbk
       _ = (2/b)*(|ak-a|+|bk-b|) := by ring

end RegularPointCoordinates

end OAI
