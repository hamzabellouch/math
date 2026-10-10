import Mathlib.Analysis.InnerProductSpace.l2Space
import OAI.Analysis.IrrationalRotation.Model.Analytic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

noncomputable section
namespace Invariant233.HilbertModelSize

open TopologicalSpace MeasureTheory
open scoped lp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem separable_of_countable_hilbertBasis {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ E) : SeparableSpace E := by
  have hs : IsSeparable (Submodule.span ℂ (Set.range b) : Set E) :=
    (Set.countable_range b).isSeparable.span
  have hc := hs.closure
  have heq : closure (Submodule.span ℂ (Set.range b) : Set E) = Set.univ := by
    change ((Submodule.span ℂ (Set.range b)).topologicalClosure : Set E) = Set.univ
    rw [b.dense_span]
    rfl
  rw [heq] at hc
  exact isSeparable_univ_iff.mp hc

theorem separable_l2 (ι : Type*) [Countable ι] : SeparableSpace (ℓ²(ι, ℂ)) :=
  separable_of_countable_hilbertBasis (default : HilbertBasis ι ℂ (ℓ²(ι, ℂ)))

theorem not_finiteDimensional_of_infinite_orthonormal {ι : Type*} [Infinite ι]
    {v : ι → E} (hv : Orthonormal ℂ v) : ¬ FiniteDimensional ℂ E := by
  intro h
  let := h
  have : Finite ι := hv.linearIndependent.finite
  exact not_finite ι

theorem not_finiteDimensional_l2 (ι : Type*) [Infinite ι] :
    ¬ FiniteDimensional ℂ (ℓ²(ι, ℂ)) :=
  not_finiteDimensional_of_infinite_orthonormal
    (default : HilbertBasis ι ℂ (ℓ²(ι, ℂ))).orthonormal

section BochnerLp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def constL2Isometry : E →ₗᵢ[ℂ] Lp E 2 μ where
  toLinearMap := Lp.constₗ 2 μ ℂ
  norm_map' x := by
    change ‖Lp.const 2 μ x‖ = ‖x‖
    rw [Lp.norm_const' 2 μ x (by norm_num) (by norm_num)]
    simp

theorem not_finiteDimensional_L2 (hE : ¬ FiniteDimensional ℂ E) :
    ¬ FiniteDimensional ℂ (Lp E 2 μ) := by
  intro h
  let := h
  exact hE (FiniteDimensional.of_injective (constL2Isometry μ).toLinearMap
    (constL2Isometry μ).injective)

theorem separable_L2_l2 [MeasurableSpace.CountablyGenerated X]
    (ι : Type*) [Countable ι] : SeparableSpace (Lp (ℓ²(ι, ℂ)) 2 μ) := by
  let := separable_l2 ι
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

theorem not_finiteDimensional_L2_l2 (ι : Type*) [Infinite ι] :
    ¬ FiniteDimensional ℂ (Lp (ℓ²(ι, ℂ)) 2 μ) :=
  not_finiteDimensional_L2 μ (not_finiteDimensional_l2 ι)

end BochnerLp

theorem circleMeasure_isProbabilityMeasure : IsProbabilityMeasure circleMeasure := by
  constructor
  change (volume : Measure Circle) Set.univ = 1
  simp [AddCircle.measure_univ]

theorem circle_representation_separable :
    SeparableSpace (Lp (ℓ²(ℤ, ℂ)) 2 circleMeasure) := by
  let := circleMeasure_isProbabilityMeasure
  exact separable_L2_l2 circleMeasure ℤ

theorem circle_representation_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (Lp (ℓ²(ℤ, ℂ)) 2 circleMeasure) := by
  let := circleMeasure_isProbabilityMeasure
  exact not_finiteDimensional_L2_l2 circleMeasure ℤ

end Invariant233.HilbertModelSize

end

end OAI
