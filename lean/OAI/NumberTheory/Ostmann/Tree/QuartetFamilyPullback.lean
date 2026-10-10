import OAI.NumberTheory.Ostmann.Tree.QuartetFamilyValue
import OAI.NumberTheory.Ostmann.Tree.QuartetRatioConvolution

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
open Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

def pairMode (bad : Bool) : PairMode := if bad then .bad else .friendly

theorem modeMultiplier_cast (bad : Bool) (d e : (ZMod p)ˣ) :
    (modeMultiplier bad d e:ZMod p) = (pairMode bad).multiplier d e := by
  cases bad
  · rfl
  · exact Units.val_inv_eq_inv_val e

theorem pairTest_zero_difference (g : ZMod p → ℂ) (hg0 : g 0=0)
    (σ : (ZMod p)ˣ) (t : ZMod p) : pairTest g σ 0 t=0 := by
  simp [pairTest,pairFirst,pairSecond,hg0]

namespace NodeInput

def crossFamilyFunction (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (a b : Bool) (m h k z : (ZMod p)ˣ) : ℂ :=
  let Q := N.crossFamily a b m h k z
  Q.parameters.evaluate g Q.D Q.Xleft Q.Xright 0 Q.leaves

theorem crossFamily_pullback_point (N : NodeInput (ZMod p) 1)
    (hcons : N.parameters.consistent) (hopp : N.parameters.bottomOpposite)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (a b : Bool) (m h k z : (ZMod p)ˣ) :
    N.crossFamilyFunction g a b m h k z =
      twoPairRatioValue (signedFunction g (parameterSign N.left a))
        (signedFunction g (parameterSign N.right b)) (orientation a) (orientation b)
        (pairMode a) (pairMode b) (N.leftLambda m a*h^2) (N.rightLambda m b*k^2)
        (N.familyRoot m) (N.familyRatioConstant m h/z^2) := by
  let Q := N.crossFamily a b m h k z
  by_cases hp : Q.pivot=0
  · change Q.parameters.evaluate g Q.D Q.Xleft Q.Xright 0 Q.leaves = _
    rw [evaluate_eq_zero Q hp g 0]
    have hr : N.familyRatioConstant m h/z^2 = 1 := by
      have he := factorRatio_zero Q hp false
      rw [crossFamily_factorRatio N a b m h k z] at he
      exact he
    rw [hr]
    simp only [twoPairRatioValue, pairMobiusValue, Units.val_one, sub_self, div_zero]
    rw [pairTest_zero_difference _ (signedFunction_zero g hg0 _)]; simp
  · change Q.parameters.evaluate g Q.D Q.Xleft Q.Xright 0 Q.leaves = _
    rw [crossFamily_value_valid N hcons hopp g hg0 a b m h k z hp 0]
    have hd : pairMobiusValue (N.familyRoot m)
        ((N.familyRatioConstant m h/z^2:(ZMod p)ˣ):ZMod p) = (Q.leftArgument hp:ZMod p) := by
      simpa only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] using
        crossFamily_left_chart N a b m h k z hp
    have he : (Q.leftArgument hp:ZMod p)-(N.familyRoot m:ZMod p) = (Q.rightArgument hp:ZMod p) := by
      rw [← hd]
      simpa only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] using
        crossFamily_right_chart N a b m h k z hp
    simp only [twoPairRatioValue, hd, he, pairValue_eq_pairTest, Units.val_mul,
      modeMultiplier_cast]
    rfl

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI
