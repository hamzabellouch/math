import Mathlib
import OAI.Analysis.FreeWords.CutAlgebra

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators

noncomputable section

variable {R ι : Type*} [NormedRing R]

theorem norm_word_le_pow (D : ι → R) (w : List ι) {t : ℝ}
    (h1 : ‖(1:R)‖ ≤ 1) (ht : 0 ≤ t) (hD : ∀ i, ‖D i‖ ≤ t) :
    ‖(w.map D).prod‖ ≤ t^w.length := by
  induction w with
  | nil => simpa using h1
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul (hD i) ih (norm_nonneg _) ht)

theorem norm_cutSum_le (C D K : ι → R) (w : List ι) {t : ℝ}
    (h1 : ‖(1:R)‖ ≤ 1) (ht : 0 ≤ t)
    (hC : ∀ i, ‖C i‖ ≤ t) (hD : ∀ i, ‖D i‖ ≤ t) (hK : ∀ i, ‖K i‖ ≤ 2) :
    ‖cutSum C D K w‖ ≤ (w.length + 1 : ℝ) * t^w.length +
      (2*w.length : ℝ) * t^(w.length-1) := by
  induction w with
  | nil => simpa [cutSum] using h1
  | cons i w ih =>
    have hprod := norm_word_le_pow D w h1 ht hD
    have hDK : ‖D i + K i‖ ≤ t+2 := (norm_add_le _ _).trans (add_le_add (hD i) (hK i))
    have h : ‖cutSum C D K (i :: w)‖ ≤
        t*((w.length+1:ℝ)*t^w.length+(2*w.length:ℝ)*t^(w.length-1)) +
          (t+2)*t^w.length := by
      apply (norm_add_le _ _).trans
      exact add_le_add ((norm_mul_le _ _).trans
        (mul_le_mul (hC i) ih (norm_nonneg _) ht))
        ((norm_mul_le _ _).trans (mul_le_mul hDK hprod (norm_nonneg _) (by positivity)))
    apply h.trans_eq
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ']
    cases hn : w.length with
    | zero => simp; ring
    | succ n => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ']; ring

theorem norm_cutSum_le_simple (C D K : ι → R) (w : List ι) {t : ℝ}
    (h1 : ‖(1:R)‖ ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hw : w ≠ [])
    (hC : ∀ i, ‖C i‖ ≤ t) (hD : ∀ i, ‖D i‖ ≤ t) (hK : ∀ i, ‖K i‖ ≤ 2) :
    ‖cutSum C D K w‖ ≤ (3*w.length+1:ℝ) * t^(w.length-1) := by
  apply (norm_cutSum_le C D K w h1 ht hC hD hK).trans
  have hn : 1 ≤ w.length := List.length_pos_iff.mpr hw
  have hp : t^w.length ≤ t^(w.length-1) := by
    have he : w.length = (w.length-1)+1 := by omega
    rw [he, Nat.add_sub_cancel, pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg ht _) ht1
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ (w.length+1:ℝ) by positivity)
  nlinarith

end

end KKFreeWords
end

end OAI
