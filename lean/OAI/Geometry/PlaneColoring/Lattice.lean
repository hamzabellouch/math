import Mathlib

namespace OAI

/-! Integer arithmetic for the classical seven-color triangular lattice. -/

namespace Problem160
namespace SevenLattice

/-- Squared Euclidean norm in a triangular lattice of unit spacing. -/
def normSq (a b : ℤ) : ℤ := a ^ 2 + a * b + b ^ 2

/-- The index-seven coloring of triangular-lattice sites. -/
def color (a b : ℤ) : ZMod 7 := (a : ZMod 7) + 3 * (b : ZMod 7)

lemma normSq_nonneg (a b : ℤ) : 0 ≤ normSq a b := by
  unfold normSq
  nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]

lemma normSq_pos {a b : ℤ} (h : a ≠ 0 ∨ b ≠ 0) : 0 < normSq a b := by
  unfold normSq
  rcases h with ha | hb
  · have ha' : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg (a + 2 * b)]
  · have hb' : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    nlinarith [sq_nonneg (2 * a + b)]

lemma seven_dvd_normSq {a b : ℤ} (h : 7 ∣ a + 3 * b) : 7 ∣ normSq a b := by
  have hi : normSq a b = (a + 3 * b) * (a - 2 * b) + 7 * b ^ 2 := by
    unfold normSq
    ring
  rw [hi]
  exact dvd_add (dvd_mul_of_dvd_left h _) (dvd_mul_right _ _)

lemma normSq_ge_seven {a b : ℤ} (h : 7 ∣ a + 3 * b)
    (hn : a ≠ 0 ∨ b ≠ 0) : 7 ≤ normSq a b := by
  exact Int.le_of_dvd (normSq_pos hn) (seven_dvd_normSq h)

lemma color_eq_iff_dvd {a b c d : ℤ} :
    color a b = color c d ↔ 7 ∣ (a - c) + 3 * (b - d) := by
  have hd := ZMod.intCast_zmod_eq_zero_iff_dvd ((a - c) + 3 * (b - d)) 7
  norm_num only [Nat.cast_ofNat] at hd
  rw [← hd]
  change color a b = color c d ↔ (((a - c) + 3 * (b - d) : ℤ) : ZMod 7) = 0
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  unfold color
  constructor <;> intro h <;> linear_combination h

lemma same_color_separation {a b c d : ℤ} (hc : color a b = color c d)
    (hne : (a, b) ≠ (c, d)) : 7 ≤ normSq (a - c) (b - d) := by
  apply normSq_ge_seven (color_eq_iff_dvd.mp hc)
  by_contra h
  push Not at h
  apply hne
  apply Prod.ext <;> omega

/-- The colors can be used directly as the `Fin 7` target of a coloring. -/
def colorFin (a b : ℤ) : Fin 7 := color a b

lemma colorFin_injective_value {a b c d : ℤ}
    (h : colorFin a b = colorFin c d) : color a b = color c d := h

end SevenLattice
end Problem160

end OAI
