import Mathlib
import OAI.Probability.BinarySweep.Representations.IrrepTransport

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G I : Type*} [Group G] [Fintype G] [Fintype I]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (σ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (σ i)]

theorem linearIndependent_classCharacters
    (hdiff : ∀ i j, Nonempty (Representation.Equiv (σ i) (σ j)) → i = j) :
    LinearIndependent ℂ (fun i => classCharacter (σ i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have h := congrArg (classPairRight (classCharacter (σ i))) ha
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
  have hi (j : I) : Nonempty (Representation.Equiv (σ i) (σ j)) ↔ i = j := by
    constructor
    · exact hdiff i j
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simp_rw [classPair_characters, hi] at h
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

theorem complete_of_card_ge [Nonempty I]
    (hdiff : ∀ i j, Nonempty (Representation.Equiv (σ i) (σ j)) → i = j)
    (hcard : Nat.card (ConjClasses G) ≤ Fintype.card I)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) [ρ.IsIrreducible] :
    ∃ i, Nonempty (Representation.Equiv ρ (σ i)) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hli := linearIndependent_classCharacters σ hdiff
  have hdim : Fintype.card I = Module.finrank ℂ (ConjClasses G → ℂ) := by
    apply le_antisymm hli.fintype_card_le_finrank
    simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using hcard
  have ht := hli.span_eq_top_of_card_eq_finrank hdim
  by_contra hn
  push Not at hn
  have hzero (i : I) : classPairRight (classCharacter ρ) (classCharacter (σ i)) = 0 := by
    have hi : ¬ Nonempty (Representation.Equiv ρ (σ i)) := fun ⟨f⟩ => (hn i).false f
    rw [classPair_characters, ite_eq_right hi]
  have hle : Submodule.span ℂ (Set.range (fun i => classCharacter (σ i))) ≤
      (classPairRight (classCharacter ρ)).ker := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hzero i
  rw [ht] at hle
  have he : classPairRight (classCharacter ρ) (classCharacter ρ) = 0 :=
    hle (Submodule.mem_top)
  rw [classPair_character_self] at he
  exact one_ne_zero he

end BinaryCoordinateSweeps.Irrep

end

end OAI
