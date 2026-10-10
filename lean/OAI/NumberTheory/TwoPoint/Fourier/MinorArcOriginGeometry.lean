import OAI.NumberTheory.TwoPoint.Fourier.MinorArcGeometric
import Mathlib.Tactic

namespace OAI

/-! Discrete interval origins: simultaneous prime windows occupy only a
bounded number of origins once the first origin is fixed. -/

namespace TwoPointCorrelations

open Finset

/-- For factors in a dyadic block, all other origins lie within three
interval lengths of the scaled first origin. This also applies to factors
`d*p`, so the same geometry survives the multiplicative correction. -/
lemma minor_arc_origin_bounds (A B H k l m : ℕ) (hA : 0 < A)
    (hB : B ≤ 2 * A) (hk : k < A * m ∧ A * m ≤ k + H)
    (hl : l < B * m ∧ B * m ≤ l + H) :
    (B * k) / A - H ≤ l ∧ l ≤ (B * k) / A + 2 * H := by
  let c := (B * k) / A
  have hlo : A * c ≤ B * k := Nat.mul_div_le _ _
  have hhi : B * k < A * (c + 1) := Nat.lt_mul_div_succ _ hA
  have hlow : c ≤ B * m := by
    by_cases hB0 : B = 0
    · simp [c, hB0]
    · have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      have hmul : A * c < A * (B * m) := by nlinarith [hk.1]
      exact (Nat.le_of_lt ((Nat.mul_lt_mul_left hA).mp hmul))
  constructor
  · change c - H ≤ l
    omega
  · change l ≤ c + 2 * H
    have hmul₁ : A * l < A * (B * m) := Nat.mul_lt_mul_of_pos_left hl.1 hA
    have hmul₂ : A * (B * m) ≤ B * k + B * H := by
      nlinarith [hk.2]
    have hmul₃ : B * H ≤ 2 * A * H := Nat.mul_le_mul_right H hB
    have hmul : A * l < A * (c + 2 * H + 1) := by nlinarith
    have := (Nat.mul_lt_mul_left hA).mp hmul
    omega

lemma minor_arc_origin_count (X A B H k m : ℕ) (hA : 0 < A)
    (hB : B ≤ 2 * A) (hk : k < A * m ∧ A * m ≤ k + H) :
    ((range X).filter (fun l => l < B * m ∧ B * m ≤ l + H)).card ≤ 3 * H + 1 := by
  have hs : (range X).filter (fun l => l < B * m ∧ B * m ≤ l + H) ⊆
      Icc ((B * k) / A - H) ((B * k) / A + 2 * H) := by
    intro l hl
    exact mem_Icc.mpr (minor_arc_origin_bounds A B H k l m hA hB hk (mem_filter.mp hl).2)
  apply (card_le_card hs).trans
  rw [Nat.card_Icc]
  omega

end TwoPointCorrelations

end OAI
