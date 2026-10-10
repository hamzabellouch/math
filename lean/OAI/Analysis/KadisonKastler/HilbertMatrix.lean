import OAI.Analysis.KadisonKastler.FaithfulRepresentation
import OAI.Analysis.FactorGeneration.Bicommutant
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

/-!
# Operator-valued matrices on finite Hilbert direct sums

This identifies the abstract C⋆-matrix norm with the operator norm on
the finite Hilbert direct sum, through a faithful star representation.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : Type*} [Fintype n] [DecidableEq n]

local instance hilbertMatrixOperatorPartialOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance hilbertMatrixOperatorStarOrderedRing : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

/-- The action of an operator-valued matrix on a finite Hilbert direct sum. -/
def hilbertMatrix (M : CStarMatrix n n (H →L[ℂ] H)) :
    Generator.FiniteHilbert n H →L[ℂ] Generator.FiniteHilbert n H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      ∑ j, (M i j).comp (PiLp.proj 2 (fun _ : n => H) j)))

omit [CompleteSpace H] [DecidableEq n] in
@[simp]
theorem hilbertMatrix_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : Generator.FiniteHilbert n H) (i : n) :
    hilbertMatrix M x i = ∑ j, M i j (x j) := by
  simp [hilbertMatrix]

omit [CompleteSpace H] [DecidableEq n] in
theorem hilbertMatrix_mul (M N : CStarMatrix n n (H →L[ℂ] H)) :
    hilbertMatrix (M * N) = hilbertMatrix M * hilbertMatrix N := by
  ext x i
  simp only [hilbertMatrix_apply, CStarMatrix.mul_apply, sum_apply,
    mul_apply_eq_comp, map_sum]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
theorem hilbertMatrix_star (M : CStarMatrix n n (H →L[ℂ] H)) :
    hilbertMatrix (star M) = star (hilbertMatrix M) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    PiLp.inner_apply, hilbertMatrix_apply, CStarMatrix.star_apply, inner_sum, sum_inner]
  rw [Finset.sum_comm]

/-- The usual matrix action is a star representation. -/
def hilbertMatrixHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₐ[ℂ]
    (Generator.FiniteHilbert n H →L[ℂ] Generator.FiniteHilbert n H) where
  toFun := hilbertMatrix
  map_one' := by
    ext x i
    simp only [hilbertMatrix_apply, CStarMatrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_mul' := hilbertMatrix_mul
  map_zero' := by ext x i; simp [hilbertMatrix_apply]
  map_add' M N := by
    ext x i
    simp [hilbertMatrix_apply, CStarMatrix.add_apply, Finset.sum_add_distrib]
  commutes' z := by
    ext x i
    simp only [hilbertMatrix_apply, CStarMatrix.algebraMap_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_star' := hilbertMatrix_star

theorem hilbertMatrixHom_injective : Function.Injective (hilbertMatrixHom (H := H) (n := n)) := by
  intro M N hMN
  ext i j x
  have h := congrArg (fun T : Generator.FiniteHilbert n H →L[ℂ] Generator.FiniteHilbert n H =>
    T (Generator.tupleSingle j x) i) hMN
  simpa [hilbertMatrixHom, hilbertMatrix_apply, Generator.tupleSingle_apply, Pi.single_apply, apply_ite] using h

/-- Abstract C⋆-matrix norms are the concrete direct-sum operator norms. -/
theorem norm_hilbertMatrix (M : CStarMatrix n n (H →L[ℂ] H)) : ‖hilbertMatrix M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map hilbertMatrixHom hilbertMatrixHom_injective M

end

end KadisonKastler

end OAI
