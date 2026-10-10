import OAI.Analysis.Nuclearity.CommutingCutZero
import OAI.Analysis.WeakInfiniteness.TensorAbsorption

namespace OAI

/-! The exact cut step in the elementary-ideal argument. A small image of
an elementary positive tensor gives an elementary tensor in the kernel. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A B D : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

private def rightEmbedding : B →⋆ₙₐ[ℂ] MinimalTensor A B where
  toFun b := minimalElementary 1 b
  map_zero' := map_zero (minimalElementaryRightLinear (1 : A))
  map_add' b c := map_add (minimalElementaryRightLinear (1 : A)) b c
  map_smul' z b := map_smul (minimalElementaryRightLinear (1 : A)) z b
  map_mul' b c := by rw [← minimalElementary_mul, one_mul]
  map_star' b := by rw [← minimalElementary_star, star_one]

theorem elementary_cut_mem_kernel (q : MinimalTensor A B →⋆ₙₐ[ℂ] D)
    (a : A) (b : B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {t : ℝ} (ht : 0 < t) (hn : ‖q (minimalElementary a b)‖ ≤ t ^ 2) :
    q (minimalElementary (MainGap.cut a t) (MainGap.cut b t)) = 0 := by
  let φ := q.comp (minimalLeftEmbedding A B)
  let ψ := q.comp (rightEmbedding (A := A))
  have hprod (x : A) (y : B) : φ x * ψ y = q (minimalElementary x y) := by
    change q (minimalElementary x 1) * q (minimalElementary 1 y) = _
    rw [← map_mul, ← minimalElementary_mul, mul_one, one_mul]
  have hc : Commute (φ a) (ψ b) := by
    change φ a * ψ b = ψ b * φ a
    rw [hprod]
    change _ = q (minimalElementary 1 b) * q (minimalElementary a 1)
    rw [← map_mul, ← minimalElementary_mul, one_mul, mul_one]
  have hz := positive_commuting_cut_product_zero (φ a) (ψ b)
    (map_nonneg φ ha) (map_nonneg ψ hb) hc ht (by simpa only [hprod] using hn)
  rw [← MainGap.map_cut φ ha ht.le, ← MainGap.map_cut ψ hb ht.le, hprod] at hz
  exact hz

end WeakPureInfiniteness

end

end OAI
