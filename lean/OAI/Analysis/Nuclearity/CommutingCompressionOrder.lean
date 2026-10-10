import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Positive

namespace OAI

/-! A positive operator decreases under compression by a commuting projection.
This is the finite-cutoff monotonicity needed for the modular-core weight. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma commuting_projection_compression_le (p a : A) (hp : IsStarProjection p)
    (ha : 0 ≤ a) (hpa : Commute p a) : p * a * p ≤ a := by
  have hpap : p * a * p = a * p := by
    rw [hpa.eq, mul_assoc, hp.isIdempotentElem.eq]
  have hid : a - p * a * p = star (1 - p) * a * (1 - p) := by
    rw [star_sub, star_one, hp.isSelfAdjoint.star_eq]
    have he : (1 - p) * a * (1 - p) = a - a * p - p * a + p * a * p := by
      noncomm_ring
    rw [he, hpap, hpa.eq]
    noncomm_ring
  apply sub_nonneg.mp
  rw [hid]
  exact star_left_conjugate_nonneg ha (1 - p)

end WeakPureInfiniteness

end

end OAI
