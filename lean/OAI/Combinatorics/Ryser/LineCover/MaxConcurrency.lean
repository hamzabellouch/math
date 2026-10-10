import OAI.Combinatorics.Ryser.LineCover.Definitions
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem exists_max_coverPencil (L : Finset (AffineLine F)) :
    ∃ p : ProjectivePoint F, ∀ r : ProjectivePoint F,
      (coverPencil L r).card ≤ (coverPencil L p).card := by
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ProjectivePoint F))
    (fun p => (coverPencil L p).card)
    ⟨Sum.inr none, Finset.mem_univ _⟩
  exact ⟨p, fun r => hp r (Finset.mem_univ r)⟩

def maxCenter (L : Finset (AffineLine F)) : ProjectivePoint F :=
  Classical.choose (exists_max_coverPencil L)

def maxConcurrency (L : Finset (AffineLine F)) : ℕ :=
  (coverPencil L (maxCenter L)).card

theorem coverPencil_card_le_maxConcurrency (L : Finset (AffineLine F))
    (p : ProjectivePoint F) : (coverPencil L p).card ≤ maxConcurrency L :=
  Classical.choose_spec (exists_max_coverPencil L) p

theorem maxConcurrency_le_card (L : Finset (AffineLine F)) :
    maxConcurrency L ≤ L.card :=
  Finset.card_le_card (coverPencil_subset L (maxCenter L))

theorem maxConcurrency_le_iff (L : Finset (AffineLine F)) (R : ℕ) :
    maxConcurrency L ≤ R ↔
      ∀ p : ProjectivePoint F, (coverPencil L p).card ≤ R := by
  constructor
  · intro h p
    exact (coverPencil_card_le_maxConcurrency L p).trans h
  · intro h
    exact h (maxCenter L)

theorem maxConcurrency_dichotomy (L : Finset (AffineLine F)) (T : ℝ) :
    (∀ p : ProjectivePoint F, ((coverPencil L p).card : ℝ) ≤ T) ∨
      ∃ p : ProjectivePoint F,
        (∀ r : ProjectivePoint F, (coverPencil L r).card ≤ (coverPencil L p).card) ∧
        T < ((coverPencil L p).card : ℝ) := by
  by_cases h : (maxConcurrency L : ℝ) ≤ T
  · exact Or.inl fun p =>
      (Nat.cast_le.mpr (coverPencil_card_le_maxConcurrency L p)).trans h
  · exact Or.inr ⟨maxCenter L, coverPencil_card_le_maxConcurrency L, lt_of_not_ge h⟩

theorem card_complement_add_card_coverPencil (L : Finset (AffineLine F))
    (p : ProjectivePoint F) :
    (L \ coverPencil L p).card + (coverPencil L p).card = L.card :=
  Finset.card_sdiff_add_card_eq_card (coverPencil_subset L p)

theorem complement_card_ge_half_of_count_bounds
    (L : Finset (AffineLine F)) (p : ProjectivePoint F) (q ρ b δ : ℝ)
    (hcount : q - b / (δ * q) ≤ (L.card : ℝ))
    (herror : b / (δ * q) ≤ ρ * q / 2)
    (hp : ((coverPencil L p).card : ℝ) < (1 - ρ) * q) :
    ρ * q / 2 ≤ ((L \ coverPencil L p).card : ℝ) := by
  have hsum : ((L \ coverPencil L p).card : ℝ) +
      ((coverPencil L p).card : ℝ) = (L.card : ℝ) := by
    exact_mod_cast card_complement_add_card_coverPencil L p
  nlinarith

theorem complement_card_ge_half_of_no_large_pencil
    (L : Finset (AffineLine F)) (q ρ b δ : ℝ)
    (hcount : q - b / (δ * q) ≤ (L.card : ℝ))
    (herror : b / (δ * q) ≤ ρ * q / 2)
    (hsmall : ∀ p : ProjectivePoint F,
      ((coverPencil L p).card : ℝ) < (1 - ρ) * q)
    (p : ProjectivePoint F) :
    ρ * q / 2 ≤ ((L \ coverPencil L p).card : ℝ) :=
  complement_card_ge_half_of_count_bounds L p q ρ b δ hcount herror (hsmall p)

end RyserCoveringCounterexample.LineCover

end

end OAI
