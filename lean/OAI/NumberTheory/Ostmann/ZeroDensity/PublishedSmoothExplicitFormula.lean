import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedComplexZeroDensity
import OAI.NumberTheory.Ostmann.Construction.SmoothPrimeMeanTest

namespace OAI

/-! # The published smooth explicit formula, for one fixed test function

H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2007),
Chapter 10: the functional equation, ordinary zero count and explicit formula.
See also H. A. Helfgott, *The ternary Goldbach problem*, Part I (15 December
2019), §§3.7.1 and 3.7.3. We use only the fixed `primeMeanTest`, supported
in [5/8,7/8]. Its Mellin transform has eighth-order decay in the fixed strip.

The formula shifts to Re(s)=-1/2, retaining the even-character residue at
zero. Its error has no dependence on an exceptional zero's distance from 1.
The count is the ordinary individual zero count summed over a finite
primitive family; there are at most Q² Dirichlet characters of conductor ≤Q.
This input contains no prime-average or favorable-prime conclusion.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothZeroTerm (Z : ∀ χ, ComplexZeroEnumeration χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (i : ℕ) : ℂ :=
  Complex.exp (((Z χ).zeros i) * (Real.log X : ℂ)) * primeMeanMellin ((Z χ).zeros i)

noncomputable def smoothTrivialZeroTerm (χ : PrimitiveComplexCharacter) : ℂ :=
  if χ.character (-1) = 1 then primeMeanMellin 0 else 0

structure PublishedSmoothExplicitFormula (Z : ∀ χ, ComplexZeroEnumeration χ) where
  errorConstant : ℝ
  errorConstant_pos : 0 < errorConstant
  mellinConstant : ℝ
  mellinConstant_pos : 0 < mellinConstant
  zeroCountConstant : ℝ
  zeroCountConstant_pos : 0 < zeroCountConstant
  mellin_decay : ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
    ‖primeMeanMellin s‖ ≤ mellinConstant * Real.exp (-8 * Real.log (1 + |s.im|))
  zero_count : ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 0 ≤ T →
    ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((Z χ).count 0 T : ℝ)) ≤
        zeroCountConstant * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2))
  absolute_summability : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
    Summable (fun i => ‖smoothZeroTerm Z χ X i‖)
  explicit_formula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
    ‖smoothMangoldtMean χ.modulus χ.character X +
      (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ ≤
        errorConstant / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))

end Ostmann

end OAI
