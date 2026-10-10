import Mathlib.Data.Nat.Squarefree
import OAI.NumberTheory.Ostmann.Characters.BonamiMonomialFamily

namespace OAI

/-! # Bonami's inequality for the actual squarefree coefficient indices -/

namespace Ostmann

open scoped BigOperators

def primeFactorSubset (P : Finset ℕ) (s : ℕ) : Finset P :=
  Finset.univ.filter (fun p => p.val ∈ s.primeFactors)

theorem mem_primeFactorSubset (P : Finset ℕ) (s : ℕ) (p : P) :
    p ∈ primeFactorSubset P s ↔ p.val ∈ s.primeFactors := by
  simp [primeFactorSubset]

theorem primeFactorSubset_map (P : Finset ℕ) (s : ℕ) (hs : s.primeFactors ⊆ P) :
    (primeFactorSubset P s).map (Function.Embedding.subtype (· ∈ P)) = s.primeFactors := by
  ext p
  simp only [Finset.mem_map, Function.Embedding.coe_subtype, mem_primeFactorSubset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hp
    exact ⟨⟨p, hs hp⟩, hp, rfl⟩

theorem primeFactorSubset_card (P : Finset ℕ) (s : ℕ) (hs : s.primeFactors ⊆ P) :
    (primeFactorSubset P s).card = s.primeFactors.card := by
  rw [← primeFactorSubset_map P s hs, Finset.card_map]

theorem primeFactorSubset_injective (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P) :
    Function.Injective (fun s : S => primeFactorSubset P s.val) := by
  intro s t hst
  apply Subtype.ext
  have hp := congrArg (fun Q : Finset P => Q.map (Function.Embedding.subtype (· ∈ P))) hst
  rw [primeFactorSubset_map P s.val (hP s s.property),
    primeFactorSubset_map P t.val (hP t t.property)] at hp
  have hh := congrArg (fun Q : Finset ℕ => ∏ p ∈ Q, p) hp
  rwa [Nat.prod_primeFactors_of_squarefree (hS s s.property),
    Nat.prod_primeFactors_of_squarefree (hS t t.property)] at hh

/-- This is the even moment bound in the manuscript, indexed by
the squarefree integers themselves. -/
theorem bonami_squarefree_family (hB : PublishedBonamiBound) (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (a : S → ℝ) (l : ℕ) (hl : 0 < l) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool,
        |∑ s : S, a s * rademacherMonomial (primeFactorSubset P s.val) ε| ^ (2 * l) ≤
      (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * (a s) ^ 2) ^ l := by
  have h := bonami_monomial_family hB P (fun s : S => primeFactorSubset P s.val)
    (primeFactorSubset_injective P S hS hP) a l hl
  simpa only [primeFactorSubset_card P _ (hP _ (Subtype.property _))] using h

end Ostmann

end OAI
