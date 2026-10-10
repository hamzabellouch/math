import OAI.Analysis.Nuclearity.CommutingCPGram

namespace OAI

/-! Positivity of a continuous linear map can be checked on squares in a
dense range. The proof is independent of the concrete tensor completion. -/

noncomputable section

namespace WeakPureInfiniteness

variable {X Y P : Type*} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
  [PartialOrder X] [StarOrderedRing X] [PartialOrder Y] [StarOrderedRing Y]

lemma continuousLinearMap_nonneg_of_dense_squares (L : X →L[ℂ] Y)
    (q : P → X) (hq : DenseRange q)
    (hsq : ∀ p, 0 ≤ L (star (q p) * q p)) (x : X) (hx : 0 ≤ x) : 0 ≤ L x := by
  have hclosed : IsClosed {z : X | (0 : Y) ≤ L (star z * z)} :=
    isClosed_le continuous_const (L.continuous.comp (continuous_star.mul continuous_id))
  have hall (z : X) : 0 ≤ L (star z * z) := hq.induction_on z hclosed hsq
  have he : star (CFC.sqrt x) * CFC.sqrt x = x := by
    rw [(CFC.sqrt_nonneg x).star_eq, CFC.sqrt_mul_sqrt_self x hx]
  simpa only [he] using hall (CFC.sqrt x)

end WeakPureInfiniteness

end

end OAI
