import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedProgressionInputs
import OAI.NumberTheory.Ostmann.ZeroDensity.RealZeroSum
import OAI.NumberTheory.Ostmann.ZeroDensity.RealPrimeSeries

namespace OAI

/-! # Published inputs for the real-character zero argument

The Hadamard input is the real-axis specialization of H. A. Helfgott,
*The ternary Goldbach problem*, Part I, 15 December 2019, section 3.7.4,
equations (3.97)--(3.102), printed pp. 86--87:
https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf .
The bounded gamma term on 1 < s <= 2 is included in the absolute constant.

The low-height region and single simple exception are H. L. Montgomery and
R. C. Vaughan, *Multiplicative Number Theory I*, Theorem 11.3 and Corollary
11.10, pp. 360 and 369, using the same decreased constant as
`PublishedProgressionInput`. The separate Siegel specialization is Corollary
11.15 of that book. All these are explicit conditional parameters.
-/

namespace Ostmann

open scoped BigOperators

structure PrimitiveRealCharacter where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℝ modulus
  primitive : character.IsPrimitive
  nontrivial : character ≠ 1

noncomputable def PrimitiveRealCharacter.complexCharacter (χ : PrimitiveRealCharacter) :
    DirichletCharacter ℂ χ.modulus := χ.character.ringHomComp Complex.ofRealHom

noncomputable def PrimitiveRealCharacter.L (χ : PrimitiveRealCharacter) : ℂ → ℂ :=
  @DirichletCharacter.LFunction χ.modulus ⟨χ.positive.ne'⟩ χ.complexCharacter

noncomputable def PrimitiveRealCharacter.logDerivative (χ : PrimitiveRealCharacter) (s : ℝ) : ℝ :=
  (deriv χ.L (s : ℂ) / χ.L (s : ℂ)).re

/-- A genuine zero sequence, indexed with multiplicities. The Hadamard
identity specifies its sum; no downstream prime-mass bound is included. -/
structure RealCharacterZeroExpansion (χ : PrimitiveRealCharacter) (C : ℝ) where
  zeros : ℕ → ℂ
  in_strip : ∀ i, 0 < (zeros i).re ∧ (zeros i).re < 1
  actual_zero : ∀ i, χ.L (zeros i) = 0
  summable : ∀ s : ℝ, 1 < s → s ≤ 2 →
    Summable (fun i => realZeroKernel (s - (zeros i).re) (zeros i).im)
  hadamard : ∀ s : ℝ, 1 < s → s ≤ 2 →
    |(∑' i, realZeroKernel (s - (zeros i).re) (zeros i).im) -
      χ.logDerivative s - (1 / 2) * Real.log χ.modulus| ≤ C

/-- Hadamard factorization and the full low-height zero-free region. Page
uniqueness for the resulting actual real zeros is already in P. -/
structure PublishedRealZeroInput (P : PublishedProgressionInput) where
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  expansion : ∀ χ : PrimitiveRealCharacter, RealCharacterZeroExpansion χ errorConstant
  region : ∀ (χ : PrimitiveRealCharacter) (Q : ℕ), 2 ≤ Q → χ.modulus ≤ Q →
    ∃ E : Finset ℕ, E.card ≤ 1 ∧
      (∀ i ∈ E, ((expansion χ).zeros i).im = 0 ∧
        1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ ((expansion χ).zeros i).re) ∧
      (∀ i ∉ E, ((expansion χ).zeros i).im ^ 2 < 1 →
        ((expansion χ).zeros i).re ≤ 1 - P.kappa / Real.log (4 * (Q : ℝ)))

/-- The one-sided real-zero consequence of Siegel's theorem, for every fixed
positive exponent. Its constant is allowed to be ineffective. -/
def PublishedSiegelBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ e : PrimitiveRealZero,
    (1 - e.beta)⁻¹ ≤ C * (e.modulus : ℝ) ^ ε

noncomputable def RealCharacterZeroExpansion.realZero {χ : PrimitiveRealCharacter} {C : ℝ}
    (Z : RealCharacterZeroExpansion χ C) (i : ℕ) (hi : (Z.zeros i).im = 0) : PrimitiveRealZero where
  modulus := χ.modulus
  positive := χ.positive
  character := χ.character
  primitive := χ.primitive
  nontrivial := χ.nontrivial
  beta := (Z.zeros i).re
  beta_pos := (Z.in_strip i).1
  beta_lt_one := (Z.in_strip i).2
  zero := by
    have he : ((Z.zeros i).re : ℂ) = Z.zeros i := by
      apply Complex.ext <;> simp [hi]
    change χ.L _ = 0
    rw [he]
    exact Z.actual_zero i

end Ostmann

end OAI
