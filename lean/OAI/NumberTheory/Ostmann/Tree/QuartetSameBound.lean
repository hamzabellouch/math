import OAI.NumberTheory.Ostmann.Tree.QuartetBlockFamily
import OAI.NumberTheory.Ostmann.Tree.QuartetBlockRoot

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Tree.Quartet
open Density
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem block_fiber_average (m : Fˣ) (f : (Leaves 2 → Fˣ) → ℝ) :
    average (fun M : {M : Leaves 2 → Fˣ // Parameters.leafProduct M=m} => f M.val) =
      average (fun B : Fˣ => average (fun h : Fˣ => average (fun k : Fˣ =>
        f (blockAssignment m B h k)))) := by
  classical
  rw [← real_average_equiv (blockFiberEquiv m) (fun M => f M.val)]
  change average (fun x : Fˣ × Fˣ × Fˣ => f (blockAssignment m x.1 x.2.1 x.2.2)) = _
  rw [real_average_prod (fun B (t : Fˣ × Fˣ) => f (blockAssignment m B t.1 t.2))]
  have ht (B : Fˣ) :
      average (fun t : Fˣ × Fˣ => f (blockAssignment m B t.1 t.2)) =
      average (fun h : Fˣ => average (fun k : Fˣ => f (blockAssignment m B h k))) :=
    real_average_prod (fun h k => f (blockAssignment m B h k))
  simp_rw [ht]

namespace NodeInput
open Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

def sameLocalMajorant (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (side : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  if side then
    8*samePairMajorant (signedFunction g (parameterSign N.right false))
      (signedFunction g (parameterSign N.left false)) 1 1 ρ⁻¹ (-y)
  else
    8*samePairMajorant (signedFunction g (parameterSign N.left false))
      (signedFunction g (parameterSign N.right false)) 1 1 ρ⁻¹ y

def untouchedLocalMajorant (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (y : ZMod p) : ℝ :=
  8*untouchedMajorant (signedFunction g (parameterSign N.left false))
    (signedFunction g (parameterSign N.right false)) 1 1 y

theorem sameLocalMajorant_nonneg (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (side : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0 ≤ N.sameLocalMajorant g side ρ y := by
  cases side <;> exact mul_nonneg (by norm_num) (samePairMajorant_nonneg _ _ _ _ _ _)

theorem untouchedLocalMajorant_nonneg (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (y : ZMod p) : 0 ≤ N.untouchedLocalMajorant g y :=
  mul_nonneg (by norm_num) (untouchedMajorant_nonneg _ _ _ _ _)

theorem sameAction_fiber_bound (N : NodeInput (ZMod p) 1)
    (hcons : N.parameters.consistent) (hopp : N.parameters.bottomOpposite)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (side : Bool) (m : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    average (fun M : {M : Leaves 2 → (ZMod p)ˣ // Parameters.leafProduct M=m} =>
      ‖mellin (fun z : (ZMod p)ˣ => N.parameters.evaluate g N.D N.Xleft N.Xright 0
        (moveSame M.val side z)) ρ‖^2) ≤ N.sameLocalMajorant g side ρ (N.familyRoot m) := by
  classical
  rw [block_fiber_average m (fun M =>
    ‖mellin (fun z : (ZMod p)ˣ => N.parameters.evaluate g N.D N.Xleft N.Xright 0
      (moveSame M side z)) ρ‖^2)]
  cases side with
  | false =>
    simp_rw [moveSame_block_left, blockFamily_value N hcons hopp g hg0]
    simpa only [sameLocalMajorant, Bool.false_eq_true, ↓reduceIte, heldPairValue,
      blockLeftArgument, blockRightArgument] using
      twoPair_same_left_root (signedFunction g (parameterSign N.left false))
        (signedFunction g (parameterSign N.right false)) 1 1
        (N.leftLambda m false) (N.rightLambda m false) (N.familyRoot m)
        (N.familyRatioConstant m 1) ρ (signedFunction_zero g hg0 _) (signedFunction_zero g hg0 _)
  | true =>
    simp_rw [moveSame_block_right, blockFamily_value N hcons hopp g hg0]
    simpa only [sameLocalMajorant, ↓reduceIte, heldPairValue,
      blockLeftArgument, blockRightArgument] using
      twoPair_same_right_root (signedFunction g (parameterSign N.left false))
        (signedFunction g (parameterSign N.right false)) 1 1
        (N.leftLambda m false) (N.rightLambda m false) (N.familyRoot m)
        (N.familyRatioConstant m 1) ρ (signedFunction_zero g hg0 _) (signedFunction_zero g hg0 _)

theorem untouched_fiber_bound (N : NodeInput (ZMod p) 1)
    (hcons : N.parameters.consistent) (hopp : N.parameters.bottomOpposite)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (m : (ZMod p)ˣ) :
    average (fun M : {M : Leaves 2 → (ZMod p)ˣ // Parameters.leafProduct M=m} =>
      ‖N.parameters.evaluate g N.D N.Xleft N.Xright 0 M.val‖^2) ≤
        N.untouchedLocalMajorant g (N.familyRoot m) := by
  classical
  rw [block_fiber_average m (fun M => ‖N.parameters.evaluate g N.D N.Xleft N.Xright 0 M‖^2)]
  simp_rw [blockFamily_value N hcons hopp g hg0]
  simpa only [untouchedLocalMajorant, heldPairValue, blockLeftArgument, blockRightArgument] using
    twoPair_untouched_root (signedFunction g (parameterSign N.left false))
      (signedFunction g (parameterSign N.right false)) 1 1
      (N.leftLambda m false) (N.rightLambda m false) (N.familyRoot m)
      (N.familyRatioConstant m 1) (signedFunction_zero g hg0 _) (signedFunction_zero g hg0 _)

end NodeInput
end Ostmann.Tree.Quartet
end

end OAI
