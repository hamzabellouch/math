import OAI.Analysis.IrrationalRotation.Product.ProductCovariance
import OAI.Analysis.IrrationalRotation.Operators.CovariantTracialVector

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem traceVector_faithfulTracial (θ : ℕ → ℝ) :
    IsFaithfulTracialVector (factor θ) traceVector := by
  have hb : (default : HilbertBasis ℤ ℂ Fiber) 0 =
      (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Fiber) 0).symm
  rw [traceVector, ← hb]
  apply FieldTraceCyclic.faithfulTracialVector_of_commuting_shiftedPullbacks
    (default : HilbertBasis ℤ ℂ Fiber) (factor θ)
    (rotationIterate θ) (rotationIterate_measurePreserving θ)
    (fun m => (WeightedShift.shift m).toLinearIsometry)
  · exact FieldKoopman.shift_default_basis
  · intro T hT
    exact commute_shiftedPullback_of_mem_factor θ hT
  · intro T hT
    obtain ⟨F, hbound, hmeas, hrepr, _⟩ := exists_unique_field hT
    exact ⟨F, hrepr, fun r => (hmeas _).aestronglyMeasurable,
      Filter.Eventually.of_forall hbound⟩

theorem vectorTrace_eq_integral_central
    (T : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    vectorTrace traceVector T =
      ∫ x, inner ℂ (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber)
        (F x (lp.single 2 (0 : ℤ) (1 : ℂ))) ∂baseMeasure :=
  FieldTraceCyclic.constant_vector_state_eq_integral T F hF _

theorem vectorTrace_mul_comm (θ : ℕ → ℝ) {A B : Hilbert →L[ℂ] Hilbert}
    (hA : A ∈ factor θ) (hB : B ∈ factor θ) :
    vectorTrace traceVector (A * B) = vectorTrace traceVector (B * A) :=
  (traceVector_faithfulTracial θ).2.1 A B hA hB

theorem eq_zero_of_positive_vectorTrace_zero (θ : ℕ → ℝ)
    {A : Hilbert →L[ℂ] Hilbert} (hA : A ∈ factor θ)
    (hpos : A.IsPositive) (hzero : vectorTrace traceVector A = 0) : A = 0 :=
  (traceVector_faithfulTracial θ).2.2 A hA hpos hzero

end Invariant233.ProductModel

end

end OAI
