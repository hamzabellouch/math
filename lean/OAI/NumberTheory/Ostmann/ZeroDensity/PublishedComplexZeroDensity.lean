import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedProgressionInputs

namespace OAI

/-! # Published zero-density and zero-free inputs for the smooth prime mean

H. L. Montgomery, *Zeros of L-functions*, Invent. Math. 8 (1969), 346–354,
Theorem 1, in the explicit form of S. Inoue, *Some explicit formulas for
partial sums of Möbius functions*, JTNB 33 (2021), 273–315, Lemma 1, p. 282:
https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1162.pdf .

The region below is the bounded-height consequence of K. Ford, B. Green,
S. Konyagin, J. Maynard and T. Tao, *Long gaps between primes*, JAMS 31
(2018), 65–105, Lemma 7.1. Deleting the whole exceptional primitive character
and replacing `Q*(1+|t|)` by `2*Q*T` only weakens that statement.
https://doi.org/10.1090/jams/876 .

These are explicit conditional parameters. The zero enumeration is shared
with the explicit-formula input; no smooth-prime-mean estimate is assumed.
-/

namespace Ostmann
open scoped Classical BigOperators

structure PrimitiveComplexCharacter where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℂ modulus
  primitive : character.IsPrimitive
  nontrivial : character ≠ 1

noncomputable def PrimitiveComplexCharacter.L (χ : PrimitiveComplexCharacter) : ℂ → ℂ :=
  @DirichletCharacter.LFunction χ.modulus ⟨χ.positive.ne'⟩ χ.character

/-- A fixed enumeration with multiplicities used by the published density
and explicit-formula statements. Bounded ordinate ranges are finite. -/
structure ComplexZeroEnumeration (χ : PrimitiveComplexCharacter) where
  zeros : ℕ → ℂ
  in_strip : ∀ i, 0 < (zeros i).re ∧ (zeros i).re < 1
  actual_zero : ∀ i, χ.L (zeros i) = 0
  finite_height : ∀ T : ℝ, {i | |(zeros i).im| ≤ T}.Finite

noncomputable def ComplexZeroEnumeration.heightIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (T : ℝ) : Finset ℕ := (Z.finite_height T).toFinset

@[simp] theorem ComplexZeroEnumeration.mem_heightIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (T : ℝ) (i : ℕ) :
    i ∈ Z.heightIndices T ↔ |(Z.zeros i).im| ≤ T := Set.Finite.mem_toFinset _

noncomputable def ComplexZeroEnumeration.count {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (σ T : ℝ) : ℕ :=
  ((Z.heightIndices T).filter (fun i => σ ≤ (Z.zeros i).re)).card

/-- The exact Montgomery–Inoue estimate, restricted to an arbitrary finite
subfamily of the primitive nonprincipal characters of conductor at most Q. -/
def PublishedComplexZeroDensity (Z : ∀ χ, ComplexZeroEnumeration χ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ), 1 ≤ Q → ∀ (T σ : ℝ), 2 ≤ T →
    1 / 2 ≤ σ → σ ≤ 1 → ∀ F : Finset PrimitiveComplexCharacter,
    (∀ χ ∈ F, χ.modulus ≤ Q) →
    (∑ χ ∈ F, ((Z χ).count σ T : ℝ)) ≤
      C * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) *
        (Real.log ((Q : ℝ) * T)) ^ 13

/-- Bounded-height Landau–Page, with the entire possible exceptional
character removed. The exception can be avoided by one prime deletion. -/
def PublishedComplexZeroRegion (Z : ∀ χ, ComplexZeroEnumeration χ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (Q : ℕ), 101 ≤ Q → ∀ T : ℝ, 2 ≤ T →
    ∃ exception : Option PrimitiveComplexCharacter,
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q → some χ ≠ exception →
      ∀ i : ℕ, |((Z χ).zeros i).im| ≤ T →
        c / Real.log (2 * (Q : ℝ) * T) ≤ 1 - ((Z χ).zeros i).re

end Ostmann

end OAI
