import OAI.Analysis.OperatorAlgebra.TracialCornerCompression
import OAI.Analysis.OperatorAlgebra.LpOperatorTensorBound
import OAI.Analysis.OperatorAlgebra.CanonicalLpOperations

namespace OAI

/-! Specialize the finite-tracial corner estimate to canonical L² operator
structures while all four operator families remain abstract. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder TensorProduct
namespace WeakPureInfiniteness
universe u
variable {J K : Type u}
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma tracial_canonical_lp_corner_sum_bound (M : VonNeumannAlgebra K)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (hE : ∃ E : (K →L[ℂ] K) →L[ℂ] (K →L[ℂ] K),
      CompletelyPositive E ∧ ‖E‖ ≤ 1 ∧
      (∀ T, E T ∈ M) ∧ (∀ T, T ∈ M → E T = T))
    (W : gnsHilbert τ.functional →ₗᵢ[ℂ] (Lp J 2 (volume : Measure ℝ)))
    (L R : M.toStarSubalgebra → (Lp J 2 (volume : Measure ℝ)) →L[ℂ] (Lp J 2 (volume : Measure ℝ)))
    (hL : ∀ a x, L a (W x) = W (gnsBundledLeft τ.functional a x))
    (hR : ∀ b x, R b (W x) = W (gnsBundledRight τ.functional τ.tracial b x))
    (hP : ∀ a b, (L a * R b) * isometricCornerProjection W = L a * R b)
    (V : K →ₗᵢ[ℂ] (Lp J 2 (volume : Measure ℝ))) (p : (Lp J 2 (volume : Measure ℝ)) →L[ℂ] (Lp J 2 (volume : Measure ℝ))) (hp : ‖p‖ ≤ 1)
    {I : Type*} [Fintype I] (a b : I → (Lp J 2 (volume : Measure ℝ)) →L[ℂ] (Lp J 2 (volume : Measure ℝ)))
    (ac bc : I → M.toStarSubalgebra)
    (ha : ∀ i, isometricCornerLift V (ac i).val = p * a i * p)
    (hb : ∀ i, isometricCornerLift V (bc i).val = p * b i * p) :
    ‖∑ i, canonicalLpOperator (L (ac i)) * canonicalLpOperator (R (bc i))‖ ≤
      ‖∑ i, minimalElementary (canonicalLpOperator (a i))
        (MulOpposite.op (canonicalLpOperator (b i)))‖ := by
  have h : hilbertOperatorTensorBound (fun i => L (ac i)) (fun i => R (bc i)) a b :=
    tracial_represented_corner_sum_bound M τ hE W L R hL hR hP V p hp a b ac bc ha hb
  exact canonicalLpOperator_tensor_bound (fun i => L (ac i)) (fun i => R (bc i)) a b h

end WeakPureInfiniteness

end

end OAI
