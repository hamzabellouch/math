import OAI.Analysis.KadisonKastler.FiniteOperatorDuality
import OAI.Analysis.KadisonKastler.IsometryComplement
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace OAI

/-! # Sharp finite coefficient factorization on an arbitrary Hilbert space

All vectors involved lie in a finite-dimensional subspace. Compression and
extension by zero preserve the dual norm, so finite-dimensional polar
duality applies without a separability assumption on the ambient space.
-/

namespace KadisonKastler

open scoped BigOperators InnerProductSpace

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def isometricOperatorLift (J : E →ₗᵢ[ℂ] H) (S : E →L[ℂ] E) : H →L[ℂ] H :=
  J.toContinuousLinearMap.comp (S.comp J.toContinuousLinearMap.adjoint)

theorem isometricOperatorLift_norm_le (J : E →ₗᵢ[ℂ] H) (S : E →L[ℂ] E) :
    ‖isometricOperatorLift J S‖ ≤ ‖S‖ := by
  calc
    _ ≤ ‖J.toContinuousLinearMap‖ * (‖S‖ * ‖J.toContinuousLinearMap.adjoint‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖S‖ * 1) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul J.norm_toContinuousLinearMap_le
        (mul_le_mul_of_nonneg_left J.norm_toContinuousLinearMap_le (norm_nonneg _))
        (by positivity) zero_le_one
    _ = ‖S‖ := by ring

theorem finiteOperatorCoefficient_lift {ι : Type*} [Fintype ι]
    (J : E →ₗᵢ[ℂ] H) (x y : ι → E) (S : E →L[ℂ] E) :
    finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i))
      (isometricOperatorLift J S) = finiteOperatorCoefficient x y S := by
  simp only [finiteOperatorCoefficient_apply, isometricOperatorLift,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    adjoint_isometry_apply, J.inner_map_map]

theorem finiteOperatorCoefficient_compress {ι : Type*} [Fintype ι]
    (J : E →ₗᵢ[ℂ] H) (x y : ι → E) (S : H →L[ℂ] H) :
    finiteOperatorCoefficient x y
      (J.toContinuousLinearMap.adjoint.comp (S.comp J.toContinuousLinearMap)) =
      finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i)) S := by
  simp only [finiteOperatorCoefficient_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact J.toContinuousLinearMap.adjoint_inner_right _ _

theorem finiteOperatorCoefficient_norm_lift {ι : Type*} [Fintype ι]
    (J : E →ₗᵢ[ℂ] H) (x y : ι → E) :
    ‖finiteOperatorCoefficient x y‖ ≤
      ‖finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro S
  rw [← finiteOperatorCoefficient_lift J x y S]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (isometricOperatorLift_norm_le J S) (norm_nonneg _))

theorem isometric_coefficient_factorization [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] (J : E →ₗᵢ[ℂ] H) (x y : ι → E) :
    ∃ (n : ℕ) (a b : Fin n → H),
      finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i)) =
        finiteOperatorCoefficient a b ∧
      (∑ i, ‖a i‖ ^ 2) ≤
        ‖finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i))‖ ∧
      (∑ i, ‖b i‖ ^ 2) ≤
        ‖finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i))‖ := by
  obtain ⟨n, a, b, he, ha, hb⟩ := finite_dimensional_coefficient_factorization x y
  refine ⟨n, fun i => J (a i), fun i => J (b i), ?_, ?_, ?_⟩
  · ext S
    rw [← finiteOperatorCoefficient_compress J x y, he,
      finiteOperatorCoefficient_compress]
  · simpa only [J.norm_map] using ha.trans (finiteOperatorCoefficient_norm_lift J x y)
  · simpa only [J.norm_map] using hb.trans (finiteOperatorCoefficient_norm_lift J x y)

/-- Every finite vector functional on an arbitrary Hilbert space admits
coefficient vectors with each squared Hilbert sum at most its dual norm. -/
theorem finite_coefficient_factorization {ι : Type*} [Fintype ι] (x y : ι → H) :
    ∃ (n : ℕ) (a b : Fin n → H),
      finiteOperatorCoefficient x y = finiteOperatorCoefficient a b ∧
      (∑ i, ‖a i‖ ^ 2) ≤ ‖finiteOperatorCoefficient x y‖ ∧
      (∑ i, ‖b i‖ ^ 2) ≤ ‖finiteOperatorCoefficient x y‖ := by
  let V := Submodule.span ℂ (Set.range x ∪ Set.range y)
  have : FiniteDimensional ℂ V :=
    FiniteDimensional.span_of_finite ℂ ((Set.finite_range x).union (Set.finite_range y))
  let x' : ι → V := fun i => ⟨x i, Submodule.subset_span (Or.inl ⟨i, rfl⟩)⟩
  let y' : ι → V := fun i => ⟨y i, Submodule.subset_span (Or.inr ⟨i, rfl⟩)⟩
  exact isometric_coefficient_factorization V.subtypeₗᵢ x' y'

end

end KadisonKastler

end OAI
