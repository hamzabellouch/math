import OAI.Combinatorics.Ryser.Geometry.AffineJoins
import OAI.Combinatorics.Ryser.LineCover.Overlap
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F]

def survivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    Finset (AffineLine F × AffineLine F) :=
  X.biUnion fun x => (L.filter (Incidence x)).offDiag

theorem mem_survivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F))
    (a b : AffineLine F) :
    (a, b) ∈ survivorPairs X L ↔
      a ∈ L ∧ b ∈ L ∧ a ≠ b ∧ ∃ x ∈ X, Incidence x a ∧ Incidence x b := by
  simp only [survivorPairs, Finset.mem_biUnion, Finset.mem_offDiag,
    Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, ⟨ha, hxa⟩, ⟨hb, hxb⟩, hab⟩
    exact ⟨ha, hb, hab, x, hx, hxa, hxb⟩
  · rintro ⟨ha, hb, hab, x, hx, hxa, hxb⟩
    exact ⟨x, hx, ⟨ha, hxa⟩, ⟨hb, hxb⟩, hab⟩

theorem survivorPairs_fibers_disjoint
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (X : Set (Point F)).PairwiseDisjoint
      (fun x => (L.filter (Incidence x)).offDiag) := by
  intro x _ y _ hxy
  apply Finset.disjoint_left.mpr
  intro p hx hy
  obtain ⟨hxa, hxb, hab⟩ := Finset.mem_offDiag.mp hx
  obtain ⟨hya, hyb, _⟩ := Finset.mem_offDiag.mp hy
  apply hxy
  exact eq_of_common_incidence_of_ne_lines hab
    (Finset.mem_filter.mp hxa).2 (Finset.mem_filter.mp hxb).2
    (Finset.mem_filter.mp hya).2 (Finset.mem_filter.mp hyb).2

theorem card_survivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (survivorPairs X L).card =
      ∑ x ∈ X, (L.filter (Incidence x)).card *
        ((L.filter (Incidence x)).card - 1) := by
  rw [survivorPairs, Finset.card_biUnion (survivorPairs_fibers_disjoint X L)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]

theorem card_survivorPairs_eq_orderedPairMass
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (survivorPairs X L).card = orderedPairMass Incidence X L := by
  rw [card_survivorPairs]
  unfold orderedPairMass multiplicity
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (fun n : ℕ => n * (n - 1))
  apply congrArg Finset.card
  ext l
  simp only [Finset.mem_filter]

def populationSurvivorPairs (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    Finset (↥L × ↥L) :=
  Finset.univ.filter fun p => (p.1.val, p.2.val) ∈ survivorPairs X L

theorem mem_populationSurvivorPairs
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ↥L × ↥L) :
    p ∈ populationSurvivorPairs X L ↔
      p.1 ≠ p.2 ∧ ∃ x ∈ X, Incidence x p.1.val ∧ Incidence x p.2.val := by
  simp only [populationSurvivorPairs, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_survivorPairs, p.1.property, p.2.property]
  exact and_congr (not_congr Subtype.val_inj) Iff.rfl

theorem card_populationSurvivorPairs
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (populationSurvivorPairs X L).card = (survivorPairs X L).card := by
  apply Finset.card_bij (fun p _ => (p.1.val, p.2.val))
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p _ q _ hpq
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpq)
    · exact Subtype.ext (congrArg Prod.snd hpq)
  · intro p hp
    have hm := (mem_survivorPairs X L p.1 p.2).mp hp
    refine ⟨(⟨p.1, hm.1⟩, ⟨p.2, hm.2.1⟩), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

theorem card_populationSurvivorPairs_eq_orderedPairMass
    (X : Finset (Point F)) (L : Finset (AffineLine F)) :
    (populationSurvivorPairs X L).card = orderedPairMass Incidence X L := by
  rw [card_populationSurvivorPairs, card_survivorPairs_eq_orderedPairMass]

end RyserCoveringCounterexample.LineCover

end

end OAI
