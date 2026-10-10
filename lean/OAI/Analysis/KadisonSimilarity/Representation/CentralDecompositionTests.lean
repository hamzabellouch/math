import OAI.Analysis.KadisonSimilarity.Representation.CentralDecomposition
import OAI.Analysis.KadisonSimilarity.Representation.CountablyGeneratedCStarAlgebra

namespace OAI

/-! # The countable tests in a central decomposition

Starting with representations of one norm-separable C-star subalgebra, their
bicommutant-generation property, and almost-everywhere agreement with the
ambient fiber representatives, the contraction tests are constructed. Only
countably many agreements are used; pointwise fiber evaluation is not
assumed to be a normal map on the von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMapWOT MeasureTheory Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

/-- Construct exactly the `test`, `test_norm`, and `test_dense` fields used
by `CentralDecompositionData`, from a separable source and its fiber
representations. -/
theorem exists_central_decomposition_tests
    (P : VonNeumannAlgebra H)
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
    [TopologicalSpace.SeparableSpace B] (hB : B ≤ P.toStarSubalgebra)
    (algebra : ∀ a, VonNeumannAlgebra (K a))
    (fiber : (vonNeumannCenter P).commutant.toStarSubalgebra → ∀ a, K a →L[ℂ] K a)
    (σ : ∀ a, B →⋆ₐ[ℂ] (K a →L[ℂ] K a))
    (hagrees : ∀ b : B, ∀ᵐ a ∂μ,
      fiber (centerCommutantInclusion P ⟨b.val, hB b.property⟩) a = σ a b)
    (hgenerates : ∀ᵐ a ∂μ, algebra a = representationVonNeumannAlgebra (σ a)) :
    ∃ test : ℕ → P.toStarSubalgebra,
      (∀ n, ‖(test n : H →L[ℂ] H)‖ ≤ 1) ∧
      ∀ᵐ a ∂μ, ∀ T : K a →L[ℂ] K a, T ∈ algebra a → ‖T‖ ≤ 1 →
        ofCLM T ∈ closure (Set.range fun n =>
          ofCLM (fiber (centerCommutantInclusion P (test n)) a)) := by
  obtain ⟨sourceTest, hnorm, hdense⟩ := exists_common_fiber_contraction_tests K σ
  let test : ℕ → P.toStarSubalgebra :=
    fun n => ⟨(sourceTest n).val, hB (sourceTest n).property⟩
  refine ⟨test, hnorm, ?_⟩
  have hagrees_all : ∀ᵐ a ∂μ, ∀ n,
      fiber (centerCommutantInclusion P (test n)) a = σ a (sourceTest n) :=
    eventually_countable_forall.mpr (fun n => hagrees (sourceTest n))
  filter_upwards [hgenerates, hagrees_all] with a hgen ha
  intro T hT hn
  have heq : (fun n => ofCLM (fiber (centerCommutantInclusion P (test n)) a)) =
      (fun n => ofCLM (σ a (sourceTest n))) := by
    funext n
    rw [ha n]
  rw [heq]
  rw [hgen] at hT
  exact hdense a T hT hn

end KadisonSimilarity

end

end OAI
