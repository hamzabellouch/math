import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersError

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset Ostmann.ZeroDensity
open scoped BigOperators

abbrev PrimitivePair := Σ q : ℕ, {χ : DirichletCharacter ℂ q // χ.IsPrimitive}

def familyToPrimitivePair {Q : ℕ} (χ : PrimitiveFamily Q) : PrimitivePair :=
  ⟨χ.1.val + 1, χ.2⟩

theorem familyToPrimitivePair_injective (Q : ℕ) :
    Function.Injective (@familyToPrimitivePair Q) := by
  intro χ ψ h
  rcases χ with ⟨⟨q, hq⟩, χ⟩
  rcases ψ with ⟨⟨r, hr⟩, ψ⟩
  have hqr : q = r := by
    have hh := congrArg Sigma.fst h
    change q+1 = r+1 at hh
    omega
  subst r
  have he : χ = ψ := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst ψ
  rfl

def primitivePairToFamily (Q : ℕ) (χ : PrimitivePair) (hpos : 0 < χ.1) (hle : χ.1 ≤ Q) :
    PrimitiveFamily Q := by
  rcases χ with ⟨q, χ⟩
  cases q with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ q => exact ⟨⟨q, by dsimp at hle; omega⟩, χ⟩

@[simp] theorem familyToPrimitivePair_toFamily (Q : ℕ) (χ : PrimitivePair)
    (hpos : 0 < χ.1) (hle : χ.1 ≤ Q) :
    familyToPrimitivePair (primitivePairToFamily Q χ hpos hle) = χ := by
  rcases χ with ⟨q, χ⟩
  cases q with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ q => rfl

@[simp] theorem primitivePairToFamily_conductor (Q : ℕ) (χ : PrimitivePair)
    (hpos : 0 < χ.1) (hle : χ.1 ≤ Q) :
    (primitivePairToFamily Q χ hpos hle).1.val + 1 = χ.1 := by
  exact congrArg Sigma.fst (familyToPrimitivePair_toFamily Q χ hpos hle)

theorem primitivePairToFamily_injective {α : Type*} (Q : ℕ) (e : α → PrimitivePair)
    (he : Function.Injective e) (hpos : ∀ i, 0 < (e i).1) (hle : ∀ i, (e i).1 ≤ Q) :
    Function.Injective (fun i => primitivePairToFamily Q (e i) (hpos i) (hle i)) := by
  intro i j hij
  apply he
  have h := congrArg familyToPrimitivePair hij
  simpa only [familyToPrimitivePair_toFamily] using h

theorem primitivePairToFamily_apply (Q : ℕ) (χ : PrimitivePair)
    (hpos : 0 < χ.1) (hle : χ.1 ≤ Q) (n : ℕ) :
    (primitivePairToFamily Q χ hpos hle).2.1 n = χ.2.1 n := by
  rcases χ with ⟨q, χ⟩
  cases q with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ q => rfl

theorem primitivePairToFamily_principal (Q : ℕ) (hQ : 1 ≤ Q) :
    primitivePairToFamily Q ⟨1, 1, DirichletCharacter.isPrimitive_one_level_one⟩
      (by decide) hQ = ⟨⟨0, by omega⟩, 1, DirichletCharacter.isPrimitive_one_level_one⟩ := rfl

end Ostmann.Supply.GroupedCharacters

end

end OAI
