import OAI.Analysis.IrrationalRotation.Operators.DenseOperatorRange
import OAI.Analysis.IrrationalRotation.Spectral.ProductWeightPolar
import OAI.Analysis.IrrationalRotation.Spectral.ProductPolarModulus
import OAI.Analysis.IrrationalRotation.Spectral.ProductQuasinilpotent

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.ProductModel

theorem weight_multiplier_selfAdjoint (θ c : ℕ → ℝ) :
    IsSelfAdjoint (star shiftOperator * weightedOperator θ c) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  exact IsSelfAdjoint.of_nonneg (realMultiplier_nonneg θ (weight θ c) 1
    (by norm_num) (measurable_weight θ c) (weight_complex_norm_le_one θ c)
    (fun x => (weight_mem_Icc θ c x).1))

theorem weightedOperator_injective (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    Function.Injective (weightedOperator θ c) := by
  intro ξ η hξη
  apply weight_multiplier_injective θ c hθ0 hc hθ
  change star shiftOperator (weightedOperator θ c ξ) =
    star shiftOperator (weightedOperator θ c η)
  rw [hξη]

theorem weight_multiplier_denseRange (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    DenseRange (star shiftOperator * weightedOperator θ c) :=
  OperatorRange.denseRange_of_selfAdjoint_injective _
    (weight_multiplier_selfAdjoint θ c) (weight_multiplier_injective θ c hθ0 hc hθ)

theorem weightedOperator_denseRange (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    DenseRange (weightedOperator θ c) := by
  have hU : shiftOperator ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
    WeightedShift.fieldShift_mem_unitary 1
  have hd := (OperatorRange.unitary_mul_selfAdjoint_range shiftOperator
    (star shiftOperator * weightedOperator θ c) hU
    (weight_multiplier_selfAdjoint θ c)
    (weight_multiplier_injective θ c hθ0 hc hθ)).2
  simpa only [← mul_assoc, (Unitary.mem_iff.mp hU).2, one_mul] using hd

theorem weightedOperator_not_surjective (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    ¬ Function.Surjective (weightedOperator θ c) := by
  apply OperatorRange.not_surjective_of_zero_mem_spectrum _
    (weightedOperator_injective θ c hθ0 hc hθ)
  rw [weightedOperator_spectrum_eq_singleton_zero θ c hθ0 hc hθ hdiv]
  exact Set.mem_singleton 0

theorem weightedOperator_range_not_closed (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    ¬ IsClosed (Set.range (weightedOperator θ c)) :=
  OperatorRange.not_isClosed_range_of_dense_not_surjective _
    (weightedOperator_denseRange θ c hθ0 hc hθ)
    (weightedOperator_not_surjective θ c hθ0 hc hθ hdiv)

theorem weightedOperator_eigenvector_eq_zero (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞)
    (z : ℂ) (ξ : Hilbert) (hξ : weightedOperator θ c ξ = z • ξ) : ξ = 0 :=
  OperatorRange.eq_zero_of_eigenvector_of_spectrum_zero _
    (weightedOperator_injective θ c hθ0 hc hθ)
    (weightedOperator_spectrum_eq_singleton_zero θ c hθ0 hc hθ hdiv) z ξ hξ

end Invariant233.ProductModel

end

end OAI
