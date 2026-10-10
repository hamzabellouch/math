import OAI.Analysis.OperatorAlgebra.GNSBundledOperators
import OAI.Analysis.OperatorAlgebra.IsometricCornerNorm

namespace OAI

/-! Finite product norms transfer through a supported GNS inclusion. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma gns_product_sum_norm (f : A →ₚ[ℂ] ℂ)
    (ht : ∀ a b, f (a * b) = f (b * a)) (V : gnsHilbert f →ₗᵢ[ℂ] H)
    (L R : A → H →L[ℂ] H)
    (hL : ∀ a x, L a (V x) = V (gnsBundledLeft f a x))
    (hR : ∀ b x, R b (V x) = V (gnsBundledRight f ht b x))
    (hP : ∀ a b, (L a * R b) * isometricCornerProjection V = L a * R b)
    {I : Type*} [Fintype I] (a b : I → A) :
    ‖∑ i, L (a i) * R (b i)‖ =
      ‖∑ i, gnsBundledLeft f (a i) * gnsBundledRight f ht (b i)‖ := by
  apply norm_eq_of_corner_intertwines V
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => hP (a i) (b i))
  · intro x
    simp only [sum_apply, mul_apply_eq_comp, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hR, hL]

end WeakPureInfiniteness

end

end OAI
