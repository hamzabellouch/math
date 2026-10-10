import OAI.Analysis.OperatorAlgebra.TracialRepresentedBound
import OAI.Analysis.Nuclearity.MinimalCornerCompression

namespace OAI

/-! Combine the finite-tracial estimate with corner compression before
specializing the concrete GNS structures. -/
noncomputable section
open scoped ComplexOrder TensorProduct
namespace WeakPureInfiniteness
universe u
variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma tracial_represented_corner_sum_bound (M : VonNeumannAlgebra K)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (hE : ∃ E : (K →L[ℂ] K) →L[ℂ] (K →L[ℂ] K),
      CompletelyPositive E ∧ ‖E‖ ≤ 1 ∧
      (∀ T, E T ∈ M) ∧ (∀ T, T ∈ M → E T = T))
    (W : gnsHilbert τ.functional →ₗᵢ[ℂ] H)
    (L R : M.toStarSubalgebra → H →L[ℂ] H)
    (hL : ∀ a x, L a (W x) = W (gnsBundledLeft τ.functional a x))
    (hR : ∀ b x, R b (W x) = W (gnsBundledRight τ.functional τ.tracial b x))
    (hP : ∀ a b, (L a * R b) * isometricCornerProjection W = L a * R b)
    (V : K →ₗᵢ[ℂ] H) (p : H →L[ℂ] H) (hp : ‖p‖ ≤ 1)
    {I : Type*} [Fintype I] (a b : I → H →L[ℂ] H)
    (ac bc : I → M.toStarSubalgebra)
    (ha : ∀ i, isometricCornerLift V (ac i).val = p * a i * p)
    (hb : ∀ i, isometricCornerLift V (bc i).val = p * b i * p) :
    ‖∑ i, L (ac i) * R (bc i)‖ ≤
      ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ :=
  (tracial_represented_sum_bound M τ hE W L R hL hR hP ac bc).trans
    (norm_minimalSum_corner_compression M V p hp a b ac bc ha hb)

end WeakPureInfiniteness

end

end OAI
