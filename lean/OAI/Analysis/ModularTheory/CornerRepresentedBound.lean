import OAI.Analysis.ModularTheory.CornerProductNorm
import OAI.Analysis.OperatorAlgebra.TracialRepresentedBound

namespace OAI

/-! The finite-tracial bound for the actual modular-corner operators. -/
noncomputable section
open MeasureTheory Filter
open scoped ComplexOrder TensorProduct
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors
variable {H A B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A] [CStarAlgebra B] [PartialOrder A] [StarOrderedRing A]
attribute [local irreducible] modularCompressedTracialState

private lemma modularCornerProduct_gnsSupport
    (S : StandardModularData H) (n : ℕ)
    (a b : (modularCompressedCorner S (n + 1)).toStarSubalgebra) :
    (isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val *
      modularTracialRightAction S
        (isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) b.val)) *
      isometricCornerProjection (modularCornerGNSInclusion S n) =
    isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val *
      modularTracialRightAction S
        (isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) b.val) := by
  rw [← modularCornerGNSInclusion_projection]
  exact modularCornerProduct_right_support S (n + 1) _ _

/-- The concrete bound is the direct specialization of the represented
finite-tracial bound, with its canonical GNS structures kept intact. -/
abbrev nuclear_quotient_modular_corner_represented_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) (n : ℕ) {I : Type*} [Fintype I]
    (a b : I → (modularCompressedCorner S (n + 1)).toStarSubalgebra) :=
  tracial_represented_sum_bound
    (H := Lp H 2 (volume : Measure ℝ))
    (K := ModularCornerHilbert (H := H) (n + 1))
    (modularCompressedCorner S (n + 1)) (modularCompressedTracialState S n)
    (nuclear_quotient_modular_corner_expectation ω hω hA q hq π S hS (n + 1))
    (modularCornerGNSInclusion S n)
    (fun a => isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val)
    (fun b => modularTracialRightAction S
      (isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) b.val))
    (modularCornerGNSInclusion_left S n) (modularCornerGNSInclusion_right S n)
    (modularCornerProduct_gnsSupport S n) a b

end WeakPureInfiniteness

end

end OAI
