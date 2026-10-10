import OAI.Analysis.IrrationalRotation.Product.ProductProjectionFields
import OAI.Analysis.IrrationalRotation.Product.ProductBaseDynamics
import OAI.Analysis.IrrationalRotation.Product.ProductWeightBridge
import OAI.Analysis.IrrationalRotation.Rotation.RealWeightedPositiveDiagonal

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233.ProductModel

theorem ae_strict_diagonal_of_invariant_projection
    {θ c : ℕ → ℝ} (hadm : AdmissibleAnglesAndCosts θ c)
    (P : Hilbert →L[ℂ] Hilbert) (hPm : P ∈ factor θ) (hP : IsStarProjection P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (hinv : (1 - P) * weightedOperator θ c * P = 0)
    (p : Base → Fiber →L[ℂ] Fiber)
    (hpbound : ∀ x, ‖p x‖ ≤ ‖P‖)
    (hpm : ∀ v, StronglyMeasurable fun x => p x v)
    (hrep : ∀ ξ : Hilbert, P ξ =ᵐ[baseMeasure] fun x => p x (ξ x)) :
    ∀ᵐ x ∂baseMeasure,
      0 < (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re ∧
      (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re < 1 := by
  let a : Base → ℤ → ℝ := fun x k => weight θ c (rotationIterate θ k x)
  have hb : ∀ x k, |a x k| ≤ 1 := by
    intro x k
    rw [abs_of_nonneg (weight_mem_Icc θ c _).1]
    exact (weight_mem_Icc θ c _).2
  have hm : ∀ k, AEStronglyMeasurable (fun x => a x k) baseMeasure := by
    intro k
    exact ((measurable_weight θ c).comp
      (rotationIterate_measurePreserving θ k).measurable).aestronglyMeasurable
  have hT : weightedOperator θ c =
      PositiveDiagonalModel.realWeightedShift a 1 (by norm_num) hb hm := by
    rfl
  have hcov : ∀ᵐ x ∂baseMeasure,
      p x * PositiveDiagonalModel.fiberShift =
        PositiveDiagonalModel.fiberShift * p (rotationIterate θ 1 x) := by
    filter_upwards [field_covariance hPm p hrep] with x hx
    exact hx 1
  have hpos : ∀ᵐ x ∂baseMeasure, 0 < a x 0 := by
    simpa only [a, rotationIterate_zero] using
      ae_weight_pos θ c (fun i => (hadm.1 i).1.le)
        (fun i => (hadm.1 i).2.2.le) hadm.2.1
  have htrace := projection_vectorTrace_mem_Ioo hPm hP hP0 hP1
  apply PositiveDiagonalModel.positive_diagonal
    (rotationIterate_ergodic hadm.2.2 (by norm_num : (1 : ℤ) ≠ 0))
    a 1 (by norm_num) hb hm hpos P p hpbound hpm hrep hP hcov
  · rwa [← hT]
  · exact htrace.1
  · exact htrace.2

theorem exists_strict_projection_field
    {θ c : ℕ → ℝ} (hadm : AdmissibleAnglesAndCosts θ c)
    (P : Hilbert →L[ℂ] Hilbert) (hPm : P ∈ factor θ) (hP : IsStarProjection P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (hinv : (1 - P) * weightedOperator θ c * P = 0) :
    ∃ p : Base → Fiber →L[ℂ] Fiber,
      (∀ x, ‖p x‖ ≤ ‖P‖) ∧
      (∀ v, StronglyMeasurable fun x => p x v) ∧
      (∀ ξ : Hilbert, P ξ =ᵐ[baseMeasure] fun x => p x (ξ x)) ∧
      (∀ᵐ x ∂baseMeasure, IsStarProjection (p x)) ∧
      (∀ᵐ x ∂baseMeasure,
        0 < (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re ∧
        (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re < 1) := by
  obtain ⟨p, hpbound, hpm, hrep, _⟩ := exists_unique_field hPm
  exact ⟨p, hpbound, hpm, hrep, field_isStarProjection hPm hP p hrep,
    ae_strict_diagonal_of_invariant_projection hadm P hPm hP hP0 hP1 hinv
      p hpbound hpm hrep⟩

end Invariant233.ProductModel

end

end OAI
