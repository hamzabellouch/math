import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.Module

namespace OAI

/-! # Algebraic constants stay independent over a transcendental field

Polynomial relations are compared coefficient by coefficient. Passing from
the polynomial algebra to its fraction field then preserves independence.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IntermediateField.algebraAdjoinAdjoin

theorem constants_linearIndependent_over_polynomial_algebra
    {F L E I J : Type*} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [Fintype J] (t : I → E) (ht : AlgebraicIndependent L t)
    (b : J → L) (hb : LinearIndependent F b) :
    LinearIndependent (Algebra.adjoin F (Set.range t))
      (fun j => algebraMap L E (b j)) := by
  classical
  have htF := ht.restrictScalars (algebraMap F L).injective
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let p (i : J) : MvPolynomial I F := htF.aevalEquiv.symm (c i)
  have hp (i : J) : MvPolynomial.aeval t (p i) = (c i : E) := by
    rw [← htF.algebraMap_aevalEquiv]
    simp [p]
  have hev (q : MvPolynomial I F) :
      (MvPolynomial.aeval t : MvPolynomial I L →ₐ[L] E)
        (MvPolynomial.map (algebraMap F L) q) = MvPolynomial.aeval t q := by
    change MvPolynomial.eval₂ (algebraMap L E) t _ =
      MvPolynomial.eval₂ (algebraMap F E) t q
    rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq F L E]
  let P : MvPolynomial I L :=
    ∑ i, MvPolynomial.C (b i) * MvPolynomial.map (algebraMap F L) (p i)
  have hPe : MvPolynomial.aeval t P = 0 := by
    simpa [P, hev, hp, Algebra.smul_def, mul_comm] using hc
  have hP : P = 0 := ht.eq_zero_of_aeval_eq_zero P hPe
  have hcoeff (d : I →₀ ℕ) (i : J) : (p i).coeff d = 0 := by
    apply Fintype.linearIndependent_iff.mp hb (fun i => (p i).coeff d) _ i
    have hh := congrArg (fun q : MvPolynomial I L => q.coeff d) hP
    simpa only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      Algebra.smul_def, mul_comm] using hh
  have hz : p j = 0 := by
    apply MvPolynomial.ext
    intro d
    simp [hcoeff]
  have hh := hp j
  rw [hz, map_zero] at hh
  exact Subtype.ext hh.symm

theorem algebraic_constants_linearIndependent_over_transcendental_field
    {F L E I J : Type*} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [Algebra.IsAlgebraic F L] [Fintype J]
    (t : I → E) (ht : AlgebraicIndependent F t)
    (b : J → L) (hb : LinearIndependent F b) :
    LinearIndependent (IntermediateField.adjoin F (Set.range t))
      (fun j => algebraMap L E (b j)) := by
  apply (LinearIndependent.iff_fractionRing
    (Algebra.adjoin F (Set.range t)) (IntermediateField.adjoin F (Set.range t))).mp
  exact constants_linearIndependent_over_polynomial_algebra t (ht.extendScalars L) b hb

end PolycyclicRecognition

end

end OAI
