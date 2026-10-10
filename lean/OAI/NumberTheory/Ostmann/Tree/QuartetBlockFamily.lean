import OAI.NumberTheory.Ostmann.Tree.QuartetFamilyPullback
import OAI.NumberTheory.Ostmann.Tree.QuartetProductFiber

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Tree.Quartet
variable {F : Type*} [Field F]

def blockAssignment (m B h k : Fˣ) : Leaves 2 → Fˣ :=
  crossAssignment false false m h k (B/h)

def blockCoordinatesEquiv : (Fˣ × Fˣ × Fˣ) ≃ (Fˣ × Fˣ × Fˣ) where
  toFun x := (x.2.1, x.2.2, x.1/x.2.1)
  invFun x := (x.2.2*x.1, x.1, x.2.1)
  left_inv x := by rcases x with ⟨B,h,k⟩; simp
  right_inv x := by rcases x with ⟨h,k,z⟩; simp

def blockFiberEquiv (m : Fˣ) :
    (Fˣ × Fˣ × Fˣ) ≃ {M : Leaves 2 → Fˣ // Parameters.leafProduct M=m} :=
  blockCoordinatesEquiv.trans (crossFiberEquiv false false m)

theorem blockFiberEquiv_apply (m B h k : Fˣ) :
    (blockFiberEquiv m (B,h,k)).val = blockAssignment m B h k := rfl

theorem blockAssignment_eq (m B h k : Fˣ) :
    blockAssignment m B h k =
      Density.join (pairAssignment false (B/h) h) (pairAssignment false ((m/B)/k) k) := by
  unfold blockAssignment crossAssignment
  have he : m/(B/h*h*k) = (m/B)/k := by simp [div_div]
  rw [he]

theorem movePair_assignment (free held z : Fˣ) :
    movePair (pairAssignment false free held) z = pairAssignment false (free*z) (held/z) := by
  simp only [movePair, pairAssignment, Bool.false_eq_true, ↓reduceIte,
    Density.left_join, Density.right_join, div_eq_mul_inv]
  rfl

theorem moveSame_block_left (m B h k z : Fˣ) :
    NodeInput.moveSame (blockAssignment m B h k) false z = blockAssignment m B (h/z) k := by
  simp only [NodeInput.moveSame, Bool.false_eq_true, ↓reduceIte, blockAssignment_eq,
    Density.left_join, Density.right_join, movePair_assignment]
  have he : B/h*z = B/(h/z) := by simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [he]

theorem moveSame_block_right (m B h k z : Fˣ) :
    NodeInput.moveSame (blockAssignment m B h k) true z = blockAssignment m B h (k/z) := by
  simp only [NodeInput.moveSame, ↓reduceIte, blockAssignment_eq,
    Density.left_join, Density.right_join, movePair_assignment]
  have he : (m/B)/k*z = (m/B)/(k/z) := by simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [he]

namespace NodeInput

theorem block_ratio_constant (N : NodeInput F 1) (m B h : Fˣ) :
    N.familyRatioConstant m h/(B/h)^2 = N.familyRatioConstant m 1/B^2 := by
  apply Units.ext
  simp only [familyRatioConstant, Units.val_div_eq_div_val, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_one]
  field_simp

open Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

def blockLeftArgument (N : NodeInput (ZMod p) 1) (m B : (ZMod p)ˣ) : ZMod p :=
  pairMobiusValue (N.familyRoot m) (N.familyRatioConstant m 1/B^2 : (ZMod p)ˣ)

def blockRightArgument (N : NodeInput (ZMod p) 1) (m B : (ZMod p)ˣ) : ZMod p :=
  N.blockLeftArgument m B-(N.familyRoot m:ZMod p)

theorem blockFamily_value (N : NodeInput (ZMod p) 1)
    (hcons : N.parameters.consistent) (hopp : N.parameters.bottomOpposite)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (m B h k : (ZMod p)ˣ) :
    N.parameters.evaluate g N.D N.Xleft N.Xright 0 (blockAssignment m B h k) =
      pairTest (signedFunction g (parameterSign N.left false)) 1 (N.blockLeftArgument m B)
        (((N.leftLambda m false*h^2:(ZMod p)ˣ):ZMod p)*N.blockLeftArgument m B) *
      pairTest (signedFunction g (parameterSign N.right false)) 1 (N.blockRightArgument m B)
        (((N.rightLambda m false*k^2:(ZMod p)ˣ):ZMod p)*N.blockRightArgument m B) := by
  have he := crossFamily_pullback_point N hcons hopp g hg0 false false m h k (B/h)
  rw [block_ratio_constant] at he
  simpa only [crossFamilyFunction, crossFamily, withLeaves, parameters, blockAssignment,
    twoPairRatioValue, blockLeftArgument, blockRightArgument, orientation, pairMode,
    Bool.false_eq_true, ↓reduceIte, PairMode.multiplier] using he

end NodeInput
end Ostmann.Tree.Quartet
end

end OAI
