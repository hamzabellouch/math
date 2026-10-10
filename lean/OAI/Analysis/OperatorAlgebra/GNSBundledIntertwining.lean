import OAI.Analysis.OperatorAlgebra.GNSBundledOperators

namespace OAI

/-! Intertwining from vector formulas, stated entirely in the bundled GNS space. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma gnsBundledLeft_intertwines (f : A →ₚ[ℂ] ℂ)
    (V : gnsHilbert f →ₗᵢ[ℂ] H) (c : ℂ) (v : A → H)
    (hV : ∀ a, V (gnsVector f a) = c • v a)
    (a : A) (T : H →L[ℂ] H) (hv : ∀ b, T (v b) = v (a * b))
    (x : gnsHilbert f) : T (V x) = V (gnsBundledLeft f a x) :=
  gns_left_intertwines_of_vector_formula f V c v hV a T hv x

lemma gnsBundledRight_intertwines (f : A →ₚ[ℂ] ℂ)
    (ht : ∀ a b, f (a * b) = f (b * a))
    (V : gnsHilbert f →ₗᵢ[ℂ] H) (c : ℂ) (v : A → H)
    (hV : ∀ a, V (gnsVector f a) = c • v a)
    (b : A) (T : H →L[ℂ] H) (hv : ∀ a, T (v a) = v (a * b))
    (x : gnsHilbert f) : T (V x) = V (gnsBundledRight f ht b x) :=
  gns_right_intertwines_of_vector_formula f ht V c v hV b T hv x

end WeakPureInfiniteness

end

end OAI
