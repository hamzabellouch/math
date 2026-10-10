import OAI.LinearAlgebra.CirculantHadamard.CyclicProjection
import OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluationAt

namespace OAI

universe uR uS

/-! Evaluation at a root of smaller order factors through the cyclic quotient. -/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
variable {m n : ℕ} [NeZero m] [NeZero n]

/-- The actual root evaluation is unchanged after reducing the cyclic index.
Both root equations are stated explicitly to match the two evaluation maps. -/
theorem evaluateAt_cyclicProjection (h : m ∣ n)
    (x : S) (hm : x ^ m = 1) (hn : x ^ n = 1) (F : Elem R n) :
    evaluateAt m x hm (cyclicProjection R h F) = evaluateAt n x hn F := by
  refine AddMonoidAlgebra.induction_linear F ?_ ?_ ?_
  · simp
  · intro F G hF hG
    change evaluateAt m x hm (cyclicProjection R h ((F : Elem R n) + G)) =
      evaluateAt n x hn ((F : Elem R n) + G)
    simp only [map_add, hF, hG]
  · intro a r
    simp only [cyclicProjection_single, evaluateAt_single]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [← pow_eq_pow_mod _ hm]

end CirculantHadamard

end

end OAI
