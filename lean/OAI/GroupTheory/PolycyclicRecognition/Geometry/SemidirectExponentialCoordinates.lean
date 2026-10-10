import OAI.GroupTheory.PolycyclicRecognition.Geometry.DerivationLieSpace
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectUnipotentRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectPolynomialRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialExponentialChart
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FaithfulRepresentationBCH
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteProductPolynomialCoordinates

namespace OAI

/-! # Polynomial exponential coordinates for the derivation extension

The chart and its inverse are retained. Thus an ordered polynomial lattice
parameter can be transported into exponential coordinates at the next step.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

theorem exists_semidirect_polynomial_exponential_coordinates :
    letI := derivationSemidirectGroup D hD
    letI : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
    ∃ Q : PolynomialExponentialCoordinates (DerivationLieSpace D hD),
    letI := Q
    ∃ E : @MulEquiv (DerivationLieSpace D hD) (L × ℝ)
      Q.group.toMul (derivationSemidirectGroup D hD).toMul,
    ∀ {u v : ℕ} (a : Module.Basis (Fin u) ℝ (DerivationLieSpace D hD))
      (c : Module.Basis (Fin v) ℝ (L × ℝ)),
      IsPolynomialInBasis a c E.toEquiv ∧ IsPolynomialInBasis c a E.toEquiv.symm := by
  let := derivationSemidirectGroup D hD
  let _ : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let _ : Monoid (L × ℝ) := (derivationSemidirectGroup D hD).toMonoid
  let := derivationSemidirectLieGroup D hD
  let N := derivationNilpotentLieModel D hD
  let b := Module.finBasis ℝ L
  let q := semidirectCoordinate b
  let := finiteDimensional_semidirectCoordinateOrbit b D hD
  let m := Module.finrank ℝ (coordinateOrbitSpan q)
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q :=
    (Module.finBasis ℝ (coordinateOrbitSpan q)).equivFun.symm
  have hq : ∀ i, ContDiff ℝ ∞ (q i) := contDiff_semidirectCoordinate b
  let ρ := coordinateMatrixRepresentation q B
  let j := coordinateMatrixDifferential q B hq
  have hi : Function.Injective ρ :=
    coordinateMatrixRepresentation_injective q B (semidirectCoordinate_injective b)
  have hj : Function.Injective j :=
    coordinateMatrixDifferential_injective q B hq (semidirectCoordinate_injective b)
  have hd := hasMFDerivAt_unitsHomLieDifferential ρ
    (contDiff_coordinateMatrixRepresentation q B hq).contMDiff
  obtain ⟨k, hk⟩ := semidirectMatrixProducts b D hD
    (derivationSemidirect_tangent_nilpotent D hD) B
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hprod (n : ℕ) (X : Fin n → GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
      (List.ofFn (fun i => groupExponential (X i))).prod =
        groupExponential (finiteDynkinPolynomial (universalDynkinCoefficients k n) X) :=
    finite_bch_of_faithful_nilpotent_representation groupExponential
      groupExponential_isGroupExponential ρ hi j hd k (fun l hl => hk l hl.le) X
  obtain ⟨Q, E, hE⟩ := polynomialExponentialCoordinates_equiv_of_finite_products
    N (derivationLieSpace_nilpotent D hD) (universalDynkinCoefficients k) hprod
  let F : @MulEquiv (DerivationLieSpace D hD) (L × ℝ)
      Q.group.toMul (derivationSemidirectGroup D hD).toMul := E
  refine ⟨Q, F, ?_⟩
  intro u v a c
  let J := j.toLinearMap.comp N.equiv.toLinearMap
  refine polynomial_chart_of_finite_matrix_exp a c F.toEquiv
    (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) J
    (hj.comp N.equiv.injective) (semidirectMatrixReadout b D hD B)
    (fun g => semidirectMatrixReadout_apply b D hD g B) ?_ ?_ k ?_
  · intro x
    change (ρ (F.toEquiv x) : Matrix (Fin m) (Fin m) ℝ) =
      NormedSpace.exp (j (N.equiv x))
    calc
      _ = (ρ (groupExponential (E := L × ℝ) (G := L × ℝ) (N.equiv x)) :
          Matrix (Fin m) (Fin m) ℝ) :=
        congrArg (fun g : L × ℝ => (ρ g : Matrix (Fin m) (Fin m) ℝ)) (hE x)
      _ = _ := congrArg Units.val (coordinateMatrixDifferential_exp q B hq (N.equiv x))
  · exact semidirectMatrixRepresentation_polynomial b D hD c B
  · intro x
    change j (N.equiv x) ^ (k + 1) = 0
    let v : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ) := N.equiv x
    have h := hk (List.replicate (k + 1) v) (by simp)
    rw [List.map_replicate, List.prod_replicate] at h
    exact h

end PolycyclicRecognition

end

end OAI
