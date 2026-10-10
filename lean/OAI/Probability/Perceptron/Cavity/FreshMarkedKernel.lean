import Mathlib
import OAI.Probability.Perceptron.Interpolation.ArrayGeometry

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

private lemma freshMarked_extension_exists {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    ∃ F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ,
      ‖F‖=‖gaussianCovarianceKernel Ψ‖ ∧
      ∀ C : CovarianceMatrix (Fin r), F C.val=gaussianCovarianceKernel Ψ C := by
  let : NormalSpace (Matrix (Fin r) (Fin r) ℝ) := inferInstanceAs (NormalSpace (Fin r→Fin r→ℝ))
  obtain ⟨F,hF,he⟩ := (gaussianCovarianceKernel Ψ).exists_extension_norm_eq_of_isClosedEmbedding
    (isClosed_matrix_posSemidef r).isClosedEmbedding_subtypeVal
  exact ⟨F,hF,fun C => congrFun he C⟩

def freshMarkedMatrixKernel {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ := Classical.choose (freshMarked_extension_exists Ψ)

lemma freshMarkedMatrixKernel_gram {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : Fin r→E) :
    freshMarkedMatrixKernel Ψ (Matrix.gram ℝ v)=
      ∫ z, Ψ z ∂multivariateGaussian 0 (Matrix.gram ℝ v) :=
  (Classical.choose_spec (freshMarked_extension_exists Ψ)).2 (gramCovariance v)

def freshMarkedArrayKernel {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    CompactArray CompactJointOverlap →ᵇ ℝ :=
  (freshMarkedMatrixKernel Ψ).compContinuous
    ⟨fun Q => fun i j : Fin r => (Q i j).1.val,by fun_prop⟩

lemma freshMarkedArrayKernel_source {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    {N k : ℕ} (x : ℕ→NormalizedSpin N×IndexedLeaf k) :
    freshMarkedArrayKernel Ψ (sourceJointArray x)=
      ∫ z, Ψ z ∂multivariateGaussian 0
        (Matrix.gram ℝ (fun i : Fin r => (x i).1.val)) := by
  change freshMarkedMatrixKernel Ψ _=_
  convert freshMarkedMatrixKernel_gram Ψ (fun i : Fin r => (x i).1.val) using 1
  congr 1

lemma freshMarkedArrayKernel_tendsto {ν : ℕ→ProbabilityMeasure (CompactArray CompactJointOverlap)}
    {ν₀ : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hν : Tendsto ν atTop (𝓝 ν₀)) {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    Tendsto (fun n => ∫ Q, freshMarkedArrayKernel Ψ Q ∂ν n) atTop
      (𝓝 (∫ Q, freshMarkedArrayKernel Ψ Q ∂ν₀)) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (freshMarkedArrayKernel Ψ)).continuousAt.tendsto.comp hν

lemma freshMarkedMatrixKernel_gaussian {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (v : Fin r→E) :
    (∫ g, Ψ (gaussianRows v g) ∂stdGaussian E) = freshMarkedMatrixKernel Ψ (Matrix.gram ℝ v) := by
  rw [freshMarkedMatrixKernel_gram,←gaussianRows_map_stdGaussian v,
    integral_map (gaussianRows v).continuous.measurable.aemeasurable Ψ.continuous.aestronglyMeasurable]

lemma freshMarkedMatrixKernel_two {r : ℕ} (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (v : Fin r→E) :
    (∫ g, Ψ (gaussianRows v g.1)*Φ (gaussianRows v g.2)
      ∂(stdGaussian E).prod (stdGaussian E)) =
      freshMarkedMatrixKernel Ψ (Matrix.gram ℝ v)*freshMarkedMatrixKernel Φ (Matrix.gram ℝ v) := by
  rw [integral_prod_mul (fun g => Ψ (gaussianRows v g)) (fun g => Φ (gaussianRows v g))]
  rw [freshMarkedMatrixKernel_gaussian,freshMarkedMatrixKernel_gaussian]

lemma twoMarkedArrayKernel_tendsto {ν : ℕ→ProbabilityMeasure (CompactArray CompactJointOverlap)}
    {ν₀ : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hν : Tendsto ν atTop (𝓝 ν₀)) {r : ℕ} (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (G : CompactArray CompactJointOverlap →ᵇ ℝ) :
    Tendsto (fun n => ∫ Q, G Q*freshMarkedArrayKernel Ψ Q*freshMarkedArrayKernel Φ Q ∂ν n) atTop
      (𝓝 (∫ Q, G Q*freshMarkedArrayKernel Ψ Q*freshMarkedArrayKernel Φ Q ∂ν₀)) := by
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (G*freshMarkedArrayKernel Ψ*freshMarkedArrayKernel Φ)).continuousAt.tendsto.comp hν

end SphericalPerceptronFreeEnergy
end

end OAI
