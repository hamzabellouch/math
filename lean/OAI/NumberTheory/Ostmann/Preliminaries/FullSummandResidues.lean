import Mathlib.Algebra.Field.ZMod
import OAI.NumberTheory.Ostmann.Preliminaries.OccupiedResidueCollision
import OAI.NumberTheory.Ostmann.Preliminaries.Residues

namespace OAI

/-! # Full forbidden residue sets in the summand-size argument -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def negativeOccupiedResidues (B : Set ℕ) (p : ℕ) : Finset (ZMod p) :=
  (occupiedResidues B p).image fun r : ℕ => -(r : ZMod p)

noncomputable def allowedSummandResidues (B : Set ℕ) (p : ℕ) [NeZero p] :
    Finset (ZMod p) := Finset.univ \ negativeOccupiedResidues B p

 theorem mem_negativeOccupiedResidues (B : Set ℕ) (p : ℕ) (hp : 0 < p) (r : ZMod p) :
    r ∈ negativeOccupiedResidues B p ↔ ∃ b ∈ B, -(b : ZMod p) = r := by
  unfold negativeOccupiedResidues
  constructor
  · intro hr
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hr
    obtain ⟨_, b, hb, hbs⟩ := mem_occupiedResidues.mp hs
    refine ⟨b, hb, ?_⟩
    rw [← hbs, ZMod.natCast_mod] at he
    exact he
  · rintro ⟨b, hb, rfl⟩
    refine Finset.mem_image.mpr ⟨b % p, ?_, ?_⟩
    · exact mem_occupiedResidues.mpr ⟨Nat.mod_lt b hp, b, hb, rfl⟩
    · rw [ZMod.natCast_mod]

 theorem negativeOccupiedResidues_card (B : Set ℕ) (p : ℕ) :
    (negativeOccupiedResidues B p).card = (occupiedResidues B p).card := by
  unfold negativeOccupiedResidues
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  have he := (ZMod.natCast_eq_natCast_iff' a b p).mp (neg_injective hab)
  rw [Nat.mod_eq_of_lt (mem_occupiedResidues.mp ha).1,
    Nat.mod_eq_of_lt (mem_occupiedResidues.mp hb).1] at he
  exact he

 theorem allowedSummandResidues_card (B : Set ℕ) (p : ℕ) [NeZero p] :
    (allowedSummandResidues B p).card + (occupiedResidues B p).card = p := by
  rw [← negativeOccupiedResidues_card B p]
  change (Finset.univ \ negativeOccupiedResidues B p).card +
    (negativeOccupiedResidues B p).card = p
  rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, ZMod.card]

 theorem EventuallyPrimeSumset.full_residue_avoidance {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ p, p.Prime → ∀ a ∈ A, N + p < a →
      (a : ZMod p) ∉ negativeOccupiedResidues B p := by
  obtain ⟨N, hN⟩ := h.prime_not_dvd_large_sum
  refine ⟨N, ?_⟩
  intro p hp a ha hlarge hr
  obtain ⟨b, hb, he⟩ := (mem_negativeOccupiedResidues B p hp.pos _).mp hr
  apply hN p hp a ha b hb (by omega) (by omega)
  apply (ZMod.natCast_eq_zero_iff (a + b) p).mp
  rw [Nat.cast_add, ← he]
  simp

 theorem occupied_to_allowed_ratio (B : Set ℕ) (p : ℕ) [NeZero p]
    (hS : (allowedSummandResidues B p).Nonempty) :
    ((occupiedResidues B p).card : ℝ) / p ≤
      (p : ℝ) / (allowedSummandResidues B p).card - 1 := by
  have hcard := allowedSummandResidues_card B p
  have hcardR : ((allowedSummandResidues B p).card : ℝ) +
      (occupiedResidues B p).card = p := by exact_mod_cast hcard
  have hSpos : (0 : ℝ) < (allowedSummandResidues B p).card := by
    exact_mod_cast hS.card_pos
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hν : (0 : ℝ) ≤ (occupiedResidues B p).card := Nat.cast_nonneg _
  calc
    _ ≤ ((occupiedResidues B p).card : ℝ) / (allowedSummandResidues B p).card :=
      div_le_div_of_nonneg_left hν hSpos (by linarith)
    _ = _ := by
      field_simp
      nlinarith

end Ostmann

end OAI
