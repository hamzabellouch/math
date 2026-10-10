import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.ReverseGuess

noncomputable def mass (s : ℝ) : List ℝ → ℝ
  | [] => 0
  | b :: bs => b / (1+s+b)^2 + mass (s+b) bs

lemma step_bound {s b : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b) :
    b / (1+s+b)^2 + 1 / (1+s+b) ≤ 1 / (1+s) := by
  have ha : 0 < 1+s := by linarith
  have hab : 0 < 1+s+b := by linarith
  calc
    b / (1+s+b)^2 + 1 / (1+s+b) ≤
        b / ((1+s)*(1+s+b)) + 1 / (1+s+b) := by
      apply add_le_add_left
      apply div_le_div_of_nonneg_left hb (mul_pos ha hab)
      nlinarith
    _ = 1 / (1+s) := by field_simp; ring

lemma mass_nonneg {s : ℝ} (hs : 0 ≤ s) (bs : List ℝ)
    (hb : ∀ b ∈ bs, 0 ≤ b) : 0 ≤ mass s bs := by
  induction bs generalizing s with
  | nil => exact le_rfl
  | cons b bs ih =>
    simp only [mass]
    exact add_nonneg (div_nonneg (hb b (by simp)) (sq_nonneg _))
      (ih (add_nonneg hs (hb b (by simp))) (fun x hx => hb x (by simp [hx])))

lemma mass_le {s : ℝ} (hs : 0 ≤ s) (bs : List ℝ)
    (hb : ∀ b ∈ bs, 0 ≤ b) : mass s bs ≤ 1/(1+s) := by
  induction bs generalizing s with
  | nil => exact div_nonneg zero_le_one (by linarith)
  | cons b bs ih =>
    have hb0 : 0 ≤ b := hb b (by simp)
    calc
      mass s (b::bs) = b/(1+s+b)^2 + mass (s+b) bs := rfl
      _ ≤ b/(1+s+b)^2 + 1/(1+(s+b)) :=
        add_le_add_right (ih (add_nonneg hs hb0) (fun x hx => hb x (by simp [hx]))) _
      _ ≤ 1/(1+s) := by simpa only [add_assoc] using step_bound hs hb0

lemma mass_zero_le_one (bs : List ℝ) (hb : ∀ b ∈ bs, 0 ≤ b) :
    mass 0 bs ≤ 1 := by simpa using mass_le (s := 0) le_rfl bs hb

end CriticalPercolation.ReverseGuess

end
end

end OAI
