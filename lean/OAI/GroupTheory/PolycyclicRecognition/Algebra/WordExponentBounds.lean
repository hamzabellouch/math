import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponents
import Mathlib.Data.Finset.Max

namespace OAI

/-! # Positive common widths for a finite bracket-word list -/

namespace PolycyclicRecognition

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every nonempty bracket word has strictly positive width if the letters do. -/
theorem bracketWordExponent_pos (s : I → ℝ) (hs : ∀ i, 0 < s i)
    (w : FreeMagma I) : 0 < bracketWordExponent s w := by
  induction w using FreeMagma.rec with
  | of i => simpa only [bracketWordExponent_of] using hs i
  | mul u v hu hv =>
    change 0 < bracketWordExponent s (u * v)
    rw [bracketWordExponent_mul]
    exact add_pos hu hv

/-- The actual finite word list has positive lower width and finite upper
width. This supplies the constants in the interior-slack margin. -/
theorem exists_positive_wordExponent_bounds (s : I → ℝ) (hs : ∀ i, 0 < s i)
    (S : Finset (FreeMagma I)) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 ≤ hi ∧
      ∀ w : S, lo ≤ bracketWordExponent s w ∧ bracketWordExponent s w ≤ hi := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image S (bracketWordExponent s) hS
    obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image S (bracketWordExponent s) hS
    exact ⟨bracketWordExponent s u, bracketWordExponent s v,
      bracketWordExponent_pos s hs u, (bracketWordExponent_pos s hs v).le,
      fun w => ⟨hmin w w.property, hmax w w.property⟩⟩
  · refine ⟨1, 0, zero_lt_one, le_rfl, ?_⟩
    intro w
    exact False.elim (hS ⟨w, w.property⟩)

/-- The free interior constant can always be chosen large enough for the
operator-norm proof, while retaining the manuscript's requirement `1 < c`. -/
theorem exists_interior_margin (m : ℕ) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ c : ℝ, 1 < c ∧ (m : ℝ) * hi < c * lo := by
  refine ⟨2 + (m : ℝ) * hi / lo, ?_, ?_⟩
  · have hp := div_nonneg (mul_nonneg (Nat.cast_nonneg m) hhi) hlo.le
    linarith
  · rw [add_mul, div_mul_cancel₀ _ hlo.ne']
    linarith

end PolycyclicRecognition

end OAI
