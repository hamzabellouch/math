import OAI.NumberTheory.TwoPoint.Bounds.ResidueCentering
import OAI.NumberTheory.TwoPoint.Bounds.GoodColumnSum

namespace OAI

/-! Identify the singleton count and reciprocal weight of actual tuple slots. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma tupleSlotLabel_occurrences {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (j : Fin J) (p : P j) :
    (labelOccurrences (tupleSlotLabel w) ⟨j, p⟩).card = (labelOccurrences (w j) p).card := by
  have he : labelOccurrences (tupleSlotLabel w) ⟨j, p⟩ =
      (labelOccurrences (w j) p).image (fun i => (i, j)) := by
    ext t
    rcases t with ⟨i, l⟩
    by_cases hl : l = j
    · subst l
      simp [labelOccurrences, tupleSlotLabel]
    · have hn : tupleSlotLabel w (i, l) ≠ ⟨j, p⟩ := by
        intro h
        exact hl (congrArg Sigma.fst h)
      simp [labelOccurrences, hn, Ne.symm hl]
  rw [he, card_image_of_injective]
  exact fun a b h => congrArg Prod.fst h

lemma tupleSlotLabel_singletons {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) :
    (singletonLabels (tupleSlotLabel w)).card = columnSingletonCount w := by
  simp only [singletonLabels, card_filter, Fintype.sum_sigma,
    tupleSlotLabel_occurrences, columnSingletonCount]

lemma tupleSlotLabel_image {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) :
    univ.image (tupleSlotLabel w) = univ.sigma (fun j => univ.image (w j)) := by
  ext z
  rcases z with ⟨j, p⟩
  simp only [mem_image, mem_univ, true_and, mem_sigma]
  constructor
  · rintro ⟨⟨i, l⟩, he⟩
    have hl : l = j := congrArg Sigma.fst he
    subst l
    exact ⟨i, by simpa only [tupleSlotLabel, Sigma.mk.inj_iff, heq_eq_eq, true_and] using he⟩
  · rintro ⟨i, hi⟩
    exact ⟨(i, j), by simp only [tupleSlotLabel, hi]⟩

/-- The baseline from singleton integration is exactly the columnwise
weight used in the universal pattern and padding sum. -/
lemma tupleSlotLabel_reciprocal {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) :
    (∏ c ∈ univ.image (tupleSlotLabel w), (c.2.val : ℝ)⁻¹) = columnReciprocalWeight w := by
  rw [tupleSlotLabel_image, prod_sigma]
  rfl

end TwoPointCorrelations

end OAI
