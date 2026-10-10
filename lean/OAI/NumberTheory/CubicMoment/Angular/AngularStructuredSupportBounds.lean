import OAI.NumberTheory.CubicMoment.Angular.AngularStructuredPartition
import OAI.NumberTheory.CubicMoment.Estimates.StructuredSupportBounds

namespace OAI

/-! The independent coordinate support bounds remain unchanged by the
fixed angular factor. Its finite sum is dominated by the original coefficient mass. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma structuredAngularPrimeSum_norm_le (ℓ : ℤ) (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) :
    ‖structuredAngularPrimeSum ℓ a b v e u W X Z‖ ≤
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Z),
        ‖primeMomentCoefficient W X Z z‖ := by
  unfold structuredAngularPrimeSum
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => _root_.norm_nonneg _))
  intro z hz
  have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Z)
    (fun i n hn => (coordinatePrimeSupport_primary W X Z i n hn).1)
    (Finset.mem_filter.mp hz).1
  rw [norm_mul,norm_mul,norm_mul,norm_theta (primary_ne_zero hp) ℓ,
    mellinPhase_norm,mul_one,mul_one]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hp _)

end CubicFirstMoment

end

end OAI
