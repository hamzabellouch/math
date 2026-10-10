import Mathlib

namespace OAI

section
namespace PartialPermutation
noncomputable section
open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
lemma character_eq_of_isConj {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {g h : G} (H : IsConj g h) :
    ρ.character g=ρ.character h := by
  obtain ⟨k,rfl⟩ := isConj_iff.mp H
  exact (ρ.char_conj _ _).symm

def classCharacter {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : ConjClasses G → ℂ :=
  Quotient.lift ρ.character (fun _ _ h => character_eq_of_isConj ρ h)

omit [Fintype G] in
lemma classCharacter_mk {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    classCharacter ρ (ConjClasses.mk g)=ρ.character g := rfl

lemma independent_classCharacters {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    [∀ i, Representation.IsIrreducible (ρ i)]
    (hd : ∀ i j, Nonempty (Representation.Equiv (ρ i) (ρ j)) ↔ i=j) :
    LinearIndependent ℂ (fun i => classCharacter (ρ i)) := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have he (g : G) : (∑ i, a i*(ρ i).character g)=0 := by
    have h := congrFun ha (ConjClasses.mk g)
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,classCharacter_mk,Pi.zero_apply] using h
  calc
    a j = ∑ i, a i * ((Nat.card G : ℂ)⁻¹ * ∑ g, (ρ i).character g * (ρ j).character g⁻¹) := by
      simp only [Representation.char_orthonormal,hd]
      simp
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g, (∑ i, a i*(ρ i).character g) * (ρ j).character g⁻¹ := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp [he]

lemma irreducible_family_card_le_conjClasses {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    [∀ i, Representation.IsIrreducible (ρ i)]
    (hd : ∀ i j, Nonempty (Representation.Equiv (ρ i) (ρ j)) ↔ i=j) :
    Fintype.card ι ≤ Nat.card (ConjClasses G) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  simpa using (independent_classCharacters V ρ hd).fintype_card_le_finrank

end
end PartialPermutation

end

end OAI
