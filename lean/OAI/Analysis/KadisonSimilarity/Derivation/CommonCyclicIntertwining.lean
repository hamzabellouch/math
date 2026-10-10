import OAI.Analysis.KadisonSimilarity.Derivation.CommonCyclicEmbedding
import OAI.Analysis.KadisonSimilarity.Representation.L2ScalarIntertwining

namespace OAI

/-! The common scalar spectral embedding intertwines the original abelian
representation with actual scalar multiplication. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

theorem cyclicCommonFamily_intertwines (i : D.generators)
    (f : C(WeakDual.characterSpace ℂ A, ℂ)) (ξ : CyclicSpectralSpace π D i) :
    cyclicCommonFamily π D i (continuousL2Mul (commutativeVectorMeasure π (i : H)) f ξ) =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) f (cyclicCommonFamily π D i ξ) := by
  unfold cyclicCommonFamily
  exact (cyclicCommonFamilyData π D i).property f ξ

theorem cyclicCommonEmbedding_intertwines (a : A) (x : H) :
    cyclicCommonEmbedding π D (π a x) =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) (gelfandStarTransform A a)
        (cyclicCommonEmbedding π D x) := by
  have hdense : Dense (Submodule.span ℂ
      (⋃ i, Set.range ((cyclicSpectralSummands π D).inclusion i)) : Set H) := by
    intro y
    change y ∈ (Submodule.span ℂ
      (⋃ i, Set.range ((cyclicSpectralSummands π D).inclusion i))).topologicalClosure
    rw [(cyclicSpectralSummands π D).dense_span]
    trivial
  have hS (i : D.generators) (ξ : CyclicSpectralSpace π D i) :
      π a ((cyclicSpectralSummands π D).inclusion i ξ) =
        (cyclicSpectralSummands π D).inclusion i
          (continuousL2Mul (commutativeVectorMeasure π (i : H)) (gelfandStarTransform A a) ξ) := by
    change π a (commutativeCyclicIsometry π (i : H) ξ) =
      commutativeCyclicIsometry π (i : H)
        (continuousL2Mul (commutativeVectorMeasure π (i : H)) (gelfandStarTransform A a) ξ)
    exact (commutativeCyclicIsometry_intertwines π (i : H) a ξ).symm
  have hsubset : (Submodule.span ℂ
      (⋃ i, Set.range ((cyclicSpectralSummands π D).inclusion i)) : Set H) ⊆
      {y | cyclicCommonEmbedding π D (π a y) =
        VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) (gelfandStarTransform A a)
          (cyclicCommonEmbedding π D y)} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, ξ, rfl⟩ := Set.mem_iUnion.mp hy
        change cyclicCommonEmbedding π D (π a ((cyclicSpectralSummands π D).inclusion i ξ)) = _
        rw [hS, cyclicCommonEmbedding_component, cyclicCommonEmbedding_component]
        exact cyclicCommonFamily_intertwines π D i (gelfandStarTransform A a) ξ
    | zero => simp
    | add y z _ _ hy hz =>
        simp only [Set.mem_ofPred_eq] at hy hz ⊢
        simp only [map_add, hy, hz]
    | smul c y _ hy =>
        simp only [Set.mem_ofPred_eq] at hy ⊢
        simp only [map_smul, hy]
  have hclosed : IsClosed {y | cyclicCommonEmbedding π D (π a y) =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) (gelfandStarTransform A a)
        (cyclicCommonEmbedding π D y)} :=
    isClosed_eq ((cyclicCommonEmbedding π D).continuous.comp (π a).continuous)
      ((VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D)
        (gelfandStarTransform A a)).continuous.comp (cyclicCommonEmbedding π D).continuous)
  exact closure_minimal hsubset hclosed (hdense x)

end KadisonSimilarity

end

end OAI
