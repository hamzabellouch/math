import OAI.Analysis.OperatorAlgebra.TracialBundledFiniteBound
import OAI.Analysis.OperatorAlgebra.GNSProductNorm

namespace OAI

/-! Apply the finite-tracial estimate through a supported GNS inclusion before
specializing the represented Hilbert spaces. -/
noncomputable section
open scoped ComplexOrder TensorProduct
namespace WeakPureInfiniteness
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma tracial_represented_sum_bound (M : VonNeumannAlgebra K)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (hE : ∃ E : (K →L[ℂ] K) →L[ℂ] (K →L[ℂ] K),
      CompletelyPositive E ∧ ‖E‖ ≤ 1 ∧
      (∀ T, E T ∈ M) ∧ (∀ T, T ∈ M → E T = T))
    (V : gnsHilbert τ.functional →ₗᵢ[ℂ] H)
    (L R : M.toStarSubalgebra → H →L[ℂ] H)
    (hL : ∀ a x, L a (V x) = V (gnsBundledLeft τ.functional a x))
    (hR : ∀ b x, R b (V x) = V (gnsBundledRight τ.functional τ.tracial b x))
    (hP : ∀ a b, (L a * R b) * isometricCornerProjection V = L a * R b)
    {I : Type*} [Fintype I] (a b : I → M.toStarSubalgebra) :
    ‖∑ i, L (a i) * R (b i)‖ ≤
      ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ :=
  (gns_product_sum_norm τ.functional τ.tracial V L R hL hR hP a b).trans_le
    (tracialBundledFiniteProduct_norm_le (H := K) M τ hE a b)

end WeakPureInfiniteness

end

end OAI
