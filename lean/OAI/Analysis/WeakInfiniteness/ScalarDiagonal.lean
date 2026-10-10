import Mathlib
import OAI.Analysis.WeakInfiniteness.FiniteGroupTensor
import OAI.Analysis.WeakInfiniteness.FreeFiniteQuotients
import OAI.Analysis.WeakInfiniteness.TensorDensity

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u

section DiagonalPolynomial

variable {G : Type u} [Group G]

def diagonalCoefficient : (G × G →₀ ℂ) →ₗ[ℂ] ℂ := by
  classical
  exact Finsupp.linearCombination ℂ (fun p => if p.1 = p.2 then 1 else 0)

lemma finite_diagonal_polynomial (F : Type u) [Group F] [Fintype F] [DecidableEq F]
    (q : G →* F) (c : G × G →₀ ℂ) :
    spatialVectorFunctional (finiteGroupSpatialRepresentation q)
      (finiteGroupSpatialDiagonal q : Completion
        (ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F)))
      (groupTensorPolynomial c).val =
      c.sum (fun p z => z • (if q p.1 = q p.2 then (1 : ℂ) else 0)) := by
  rw [groupTensorPolynomial_val]
  simp only [Finsupp.sum, map_sum, map_smul, finiteGroupSpatialDiagonal_coefficient]

lemma finite_diagonal_polynomial_bound (F : Type u) [Group F] [Fintype F] [DecidableEq F]
    (q : G →* F) (c : G × G →₀ ℂ) :
    ‖c.sum (fun p z => z • (if q p.1 = q p.2 then (1 : ℂ) else 0))‖ ≤
      ‖groupTensorPolynomial c‖ := by
  rw [← finite_diagonal_polynomial F q c]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  have hb := norm_spatialVectorFunctional_le (finiteGroupSpatialRepresentation q)
    (finiteGroupSpatialDiagonal q : Completion
      (ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F)))
  simp only [Completion.norm_coe, norm_finiteGroupSpatialDiagonal, one_mul] at hb
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)

end DiagonalPolynomial

section FreeDiagonal

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma norm_free_diagonalCoefficient_le (c : FreeGroup α × FreeGroup α →₀ ℂ) :
    ‖diagonalCoefficient c‖ ≤ ‖groupTensorPolynomial c‖ := by
  classical
  let S := c.support.image Prod.fst ∪ c.support.image Prod.snd
  obtain ⟨m, hm⟩ := freeFiniteQuotient_injOn_finset S
  have heq (p : FreeGroup α × FreeGroup α) (hp : p ∈ c.support) :
      freeFiniteQuotient m p.1 = freeFiniteQuotient m p.2 ↔ p.1 = p.2 := by
    constructor
    · exact hm (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
    · rintro h; rw [h]
  have hv : diagonalCoefficient c = c.sum (fun p z =>
      z • (if freeFiniteQuotient m p.1 = freeFiniteQuotient m p.2 then (1 : ℂ) else 0)) := by
    simp only [diagonalCoefficient, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : p.1 = p.2
    · simp [h]
    · simp [h, not_congr (heq p hp)]
  rw [hv]
  exact finite_diagonal_polynomial_bound _ (freeFiniteQuotient m) c

def freeDiagonalFunctional :
    MinimalTensor (FullGroupAlgebra (FreeGroup α)) (FullGroupAlgebra (FreeGroup α)) →L[ℂ] ℂ :=
  diagonalCoefficient.extendOfNorm groupTensorPolynomial

lemma freeDiagonalFunctional_polynomial (c : FreeGroup α × FreeGroup α →₀ ℂ) :
    freeDiagonalFunctional (groupTensorPolynomial c) = diagonalCoefficient c := by
  apply LinearMap.extendOfNorm_eq groupTensorPolynomial_dense
  exact ⟨1, fun c => by simpa only [one_mul] using norm_free_diagonalCoefficient_le c⟩

lemma norm_freeDiagonalFunctional_le : ‖freeDiagonalFunctional (α := α)‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le groupTensorPolynomial_dense zero_le_one
  intro c
  simpa only [one_mul] using norm_free_diagonalCoefficient_le c

lemma freeDiagonalFunctional_group_tensors (s t : FreeGroup α) :
    freeDiagonalFunctional (minimalElementary (fullGroupElement s) (fullGroupElement t)) =
      if s = t then (1 : ℂ) else 0 := by
  have h := freeDiagonalFunctional_polynomial (Finsupp.single (s,t) 1)
  by_cases hst : s = t
  · simpa [hst, groupTensorPolynomial, diagonalCoefficient, Finsupp.linearCombination_single] using h
  · simpa [hst, groupTensorPolynomial, diagonalCoefficient, Finsupp.linearCombination_single] using h

end FreeDiagonal

end WeakPureInfiniteness
end

end OAI
