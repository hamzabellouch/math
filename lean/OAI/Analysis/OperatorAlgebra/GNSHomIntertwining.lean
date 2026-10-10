import OAI.Analysis.OperatorAlgebra.GNSBundledIntertwining

namespace OAI

/-! The vector-formula intertwiner for a multiplicative represented action. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma gnsBundledLeft_intertwines_hom (f : A →ₚ[ℂ] ℂ)
    (V : gnsHilbert f →ₗᵢ[ℂ] H) (c : ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hV : ∀ a, V (gnsVector f a) = c • π a ξ)
    (a : A) (x : gnsHilbert f) :
    π a (V x) = V (gnsBundledLeft f a x) := by
  refine gnsBundledLeft_intertwines f V c (fun b => π b ξ) hV a (π a) ?_ x
  intro b
  exact congrArg (fun T : H →L[ℂ] H => T ξ) (map_mul π a b).symm

end WeakPureInfiniteness

end

end OAI
