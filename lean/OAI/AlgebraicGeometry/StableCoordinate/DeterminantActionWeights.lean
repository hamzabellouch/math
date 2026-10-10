import OAI.AlgebraicGeometry.StableCoordinate.ActionWeightDerivative
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantGradedObstruction

namespace OAI

/-!
# The differentiated lifted action preserves the actual fiber grading

This is the last interface in the manuscript's Proposition `prop:lift`.
Once a normalized frame lift supplies the five coordinate coefficient laws,
this file proves equivariance of its entire algebra homomorphism and hence
preservation of every actual fiber-weight submodule after differentiation.
The five identities are consumed as construction outputs, not as additional
assumptions of the principal target; existence of the lifted action is separate.
-/

namespace StableCoordinate.DeterminantActionWeights

open MvPolynomial
open DeterminantRing
open ActionWeightDerivative

noncomputable section

variable (k : Type*) [CommRing k]

/-- The actual five quotient generators generate the determinant algebra. -/
theorem generator_adjoin_eq_top :
    Algebra.adjoin k (Set.range (generator k)) = ⊤ := by
  have hm : aeval (generator k) = mk k := by
    ext i
    simp [generator]
  rw [← MvPolynomial.aeval_range, hm, AlgHom.range_eq_top]
  exact Ideal.Quotient.mk_surjective

/-- Coordinatewise coefficient weights imply full equivariance of the actual
polynomial algebra homomorphism on the determinant quotient. -/
theorem commutesWithWeights_of_generator_coefficients
    (α : C k →ₐ[k] Polynomial (C k))
    (hα : ∀ (i : Fin 5) (m : ℕ),
      DeterminantWeights.fiberCoaction k ((α (generator k i)).coeff m) =
        AddMonoidAlgebra.single (Obstruction.fiberWeight i)
          ((α (generator k i)).coeff m)) :
    CommutesWithWeights (DeterminantWeights.fiberCoaction k) α :=
  commutesWithWeights_of_generators (DeterminantWeights.fiberCoaction k) α
    (generator k) Obstruction.fiberWeight (generator_adjoin_eq_top k)
    (DeterminantWeights.fiberCoaction_generator k) hα

/-- Every coefficient of the lifted polynomial family preserves every piece
of the *constructed* fiber grading, not only the five generator weights. -/
theorem coefficient_preserves_fiberPiece
    (α : C k →ₐ[k] Polynomial (C k))
    (hα : ∀ (i : Fin 5) (m : ℕ),
      DeterminantWeights.fiberCoaction k ((α (generator k i)).coeff m) =
        AddMonoidAlgebra.single (Obstruction.fiberWeight i)
          ((α (generator k i)).coeff m))
    {n : ℤ} {q : C k} (hq : q ∈ Obstruction.fiberPiece k n) (m : ℕ) :
    (α q).coeff m ∈ Obstruction.fiberPiece k n := by
  apply (DeterminantGradedObstruction.mem_fiberPiece_iff_fiberCoaction k n).mpr
  apply coeff_preserves_weight (DeterminantWeights.fiberCoaction k) α
    (commutesWithWeights_of_generator_coefficients k α hα)
  exact (DeterminantGradedObstruction.mem_fiberPiece_iff_fiberCoaction k n).mp hq

/-- Differentiation of the actual lifted polynomial family preserves the
fiber grading required in the rigidity theorem. -/
theorem derivation_preserves_fiberPiece
    (α : C k →ₐ[k] Polynomial (C k))
    (hα : ∀ (i : Fin 5) (m : ℕ),
      DeterminantWeights.fiberCoaction k ((α (generator k i)).coeff m) =
        AddMonoidAlgebra.single (Obstruction.fiberWeight i)
          ((α (generator k i)).coeff m))
    (D : Derivation k (C k) (C k)) (hD : ∀ q, D q = (α q).coeff 1) :
    ∀ (n : ℤ) (q : C k), q ∈ Obstruction.fiberPiece k n →
      D q ∈ Obstruction.fiberPiece k n := by
  intro n q hq
  rw [hD]
  exact coefficient_preserves_fiberPiece k α hα hq 1

/-- Read the coordinate coefficient laws in the manuscript's names and order.
This is the interface supplied by the normalized-frame scaling calculation. -/
theorem generator_laws_of_five_coefficients
    (α : C k →ₐ[k] Polynomial (C k))
    (ha : ∀ m, DeterminantWeights.fiberCoaction k ((α (a k)).coeff m) =
      AddMonoidAlgebra.single 1 ((α (a k)).coeff m))
    (hd : ∀ m, DeterminantWeights.fiberCoaction k ((α (d k)).coeff m) =
      AddMonoidAlgebra.single 1 ((α (d k)).coeff m))
    (hb : ∀ m, DeterminantWeights.fiberCoaction k ((α (b k)).coeff m) =
      AddMonoidAlgebra.single (-1) ((α (b k)).coeff m))
    (hc : ∀ m, DeterminantWeights.fiberCoaction k ((α (c k)).coeff m) =
      AddMonoidAlgebra.single (-1) ((α (c k)).coeff m))
    (hu : ∀ m, DeterminantWeights.fiberCoaction k ((α (u k)).coeff m) =
      AddMonoidAlgebra.single 0 ((α (u k)).coeff m)) :
    ∀ (i : Fin 5) (m : ℕ),
      DeterminantWeights.fiberCoaction k ((α (generator k i)).coeff m) =
        AddMonoidAlgebra.single (Obstruction.fiberWeight i)
          ((α (generator k i)).coeff m) := by
  intro i m
  fin_cases i
  · simpa [Obstruction.fiberWeight, a] using ha m
  · simpa [Obstruction.fiberWeight, d] using hd m
  · simpa [Obstruction.fiberWeight, b] using hb m
  · simpa [Obstruction.fiberWeight, c] using hc m
  · simpa [Obstruction.fiberWeight, u] using hu m

end
end StableCoordinate.DeterminantActionWeights

end OAI
