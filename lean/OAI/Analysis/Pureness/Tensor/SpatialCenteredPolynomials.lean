import OAI.Analysis.Pureness.Tensor.SpatialExpectationKernel
import OAI.Analysis.Pureness.Tensor.SpatialGroupPolynomialMap

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
local instance spatialCenteredPolynomialsDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

include hα in
lemma spatialCoefficientExpectation_norm_le
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    ‖spatialCoefficientExpectation (G := G) α x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖spatialGroupFourier α (1 : G) x‖*‖(1 : reducedGroupAlgebra G)‖ :=
      spatialCompletionMap_tmul_norm_le α _ _ _
    _ ≤ ‖spatialGroupFourier α (1 : G) x‖*1 :=
      mul_le_mul_of_nonneg_left (by exact ContinuousLinearMap.norm_id_le) (norm_nonneg _)
    _ ≤ ‖x‖ := by rw [mul_one]; exact spatialGroupFourier_norm_le α hα 1 x

def centeredGroupPolynomial (a : G →₀ A) : G →₀ A := a-Finsupp.single 1 (a 1)

lemma centeredGroupPolynomial_one (a : G →₀ A) : centeredGroupPolynomial a 1 = 0 := by
  simp [centeredGroupPolynomial]

include hα in
lemma spatialGroupPolynomialMap_centered (a : G →₀ A) :
    spatialGroupPolynomialMap (G := G) α (centeredGroupPolynomial a) =
      spatialGroupPolynomialMap (G := G) α a-
        spatialCoefficientExpectation (G := G) α (spatialGroupPolynomialMap (G := G) α a) := by
  have he : spatialCoefficientExpectation (G := G) α (spatialGroupPolynomialMap (G := G) α a) =
      spatialCompletionMap α (reducedGroupAlgebra G).subtype (a 1 ⊗ₜ[ℂ] 1) :=
    congrArg (spatialTensorLeftLeg α (reducedGroupAlgebra G).subtype 1)
      (spatialGroupPolynomialMap_fourier (G := G) α hα a 1)
  have hu : (reducedGroupUnitary G 1 : reducedGroupAlgebra G) = 1 := by
    simp only [map_one,OneMemClass.coe_one]
  have hs := (spatialGroupPolynomialMap_single (G := G) α (1 : G) (a 1)).trans
    (congrArg (fun b : reducedGroupAlgebra G =>
      spatialCompletionMap α (reducedGroupAlgebra G).subtype (a 1 ⊗ₜ[ℂ] b)) hu)
  exact (map_sub (spatialGroupPolynomialMap (G := G) α) a (Finsupp.single 1 (a 1))).trans
    (congrArg (fun t => spatialGroupPolynomialMap (G := G) α a-t) (hs.trans he.symm))

private lemma exists_centered_approximation {P V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (p : P → V) (c : P → P) (e : V →L[ℂ] V) (hdense : DenseRange p)
    (hc : ∀ a, p (c a) = p a - e (p a)) (he : ∀ v, ‖e v‖ ≤ ‖v‖)
    (x : V) (hx : e x = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ a, ‖x - p (c a)‖ < ε := by
  obtain ⟨a, ha⟩ := hdense.exists_dist_lt x (half_pos hε)
  have hdist : ‖x - p a‖ < ε / 2 := by
    simpa only [dist_eq_norm] using ha
  have hbound : ‖e (p a)‖ ≤ ‖x - p a‖ := by
    simpa only [map_sub, hx, zero_sub, norm_neg] using he (x - p a)
  refine ⟨a, ?_⟩
  rw [hc]
  calc
    ‖x - (p a - e (p a))‖ = ‖(x - p a) + e (p a)‖ := by congr 1; abel
    _ ≤ ‖x - p a‖ + ‖e (p a)‖ := norm_add_le _ _
    _ < ε := by linarith

include hα in

theorem exists_centered_spatial_polynomial
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype)
    (hx : spatialGroupFourier α (1 : G) x = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : G →₀ A, a 1 = 0 ∧ ‖x-spatialGroupPolynomialMap (G := G) α a‖ < ε := by
  have he : spatialCoefficientExpectation (G := G) α x = 0 :=
    (congrArg (spatialTensorLeftLeg α (reducedGroupAlgebra G).subtype 1) hx).trans
      (map_zero _)
  have happrox : ∃ a : G →₀ A,
      ‖x - spatialGroupPolynomialMap (G := G) α (centeredGroupPolynomial a)‖ < ε :=
    exists_centered_approximation
    (P := G →₀ A) (V := representedSpatialTensor α (reducedGroupAlgebra G).subtype)
    (spatialGroupPolynomialMap (G := G) α) centeredGroupPolynomial
    (spatialCoefficientExpectation (G := G) α)
    (spatialGroupPolynomialMap_denseRange (G := G) α)
    (spatialGroupPolynomialMap_centered (G := G) α hα)
    (spatialCoefficientExpectation_norm_le (G := G) α hα) x he ε hε
  obtain ⟨a, ha⟩ := happrox
  exact ⟨centeredGroupPolynomial a, centeredGroupPolynomial_one a, ha⟩
end CuntzPureness

end

end OAI
