import OAI.NumberTheory.Ostmann.Tree.QuartetFamilyParameters

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
variable {F : Type*} [Field F]

def parameterSign (P : Parameters F 1) (freeRight : Bool) : Bool :=
  match P with
  | .branch _ _ _ _ L R =>
    if freeRight then NodeInput.leafSign R else NodeInput.leafSign L

namespace NodeInput

theorem leftNode_sign (N : NodeInput F 1) (hp : N.pivot ≠ 0) (a : Bool) :
    (N.leftNode hp).orientedSign a = parameterSign N.left a := by
  cases he : N.left
  simp only [leftNode, he, orientedSign, parameterSign]

theorem rightNode_sign (N : NodeInput F 1) (hp : N.pivot ≠ 0) (b : Bool) :
    (N.rightNode hp).orientedSign b = parameterSign N.right b := by
  cases he : N.right
  simp only [rightNode, he, orientedSign, parameterSign]

theorem crossFamily_value_valid (N : NodeInput F 1) (hcons : N.parameters.consistent)
    (hopp : N.parameters.bottomOpposite) (g : F → ℂ) (hg0 : g 0=0)
    (a b : Bool) (m h k z : Fˣ) (hp : (N.crossFamily a b m h k z).pivot ≠ 0)
    (incoming : F) :
    let Q := N.crossFamily a b m h k z
    Q.parameters.evaluate g Q.D Q.Xleft Q.Xright incoming Q.leaves =
      pairValue g (parameterSign N.left a) (orientation a) (Q.leftArgument hp:F)
        (((N.leftLambda m a*h^2)*modeMultiplier a (Q.leftArgument hp) (Q.rightArgument hp):Fˣ):F) *
      pairValue g (parameterSign N.right b) (orientation b) (Q.rightArgument hp:F)
        (((N.rightLambda m b*k^2)*modeMultiplier b (Q.rightArgument hp) (Q.leftArgument hp):Fˣ):F) := by
  dsimp only
  let Q := N.crossFamily a b m h k z
  have hc : N.left.childConsistent (N.u*N.a) ∧ N.right.childConsistent (N.u*N.b) ∧
      N.left.consistent ∧ N.right.consistent := hcons
  have hs : N.left.bottomOpposite ∧ N.right.bottomOpposite := hopp
  have hsL : (Q.leftNode hp).parameters.bottomOpposite := by
    rw [leftNode_parameters]
    exact hs.1
  have hsR : (Q.rightNode hp).parameters.bottomOpposite := by
    rw [rightNode_parameters]
    exact hs.2
  have he := descend_evaluate Q hp g incoming
  rw [bottom_evaluate_all _ hsL g hg0 _ a, bottom_evaluate_all _ hsR g hg0 _ b,
    leftNode_argument Q hp hc.1, rightNode_argument Q hp hc.2.1,
    leftNode_sign, rightNode_sign,
    crossFamily_left_parameter N hcons a b m h k z hp,
    crossFamily_right_parameter N hcons a b m h k z hp] at he
  exact he

theorem crossFamily_factorRatio (N : NodeInput F 1) (a b : Bool) (m h k z : Fˣ) :
    (N.crossFamily a b m h k z).factorRatio false = N.familyRatioConstant m h/z^2 := by
  change ratio (N.crossFamily a b m h k z).left.frequency
    (N.crossFamily a b m h k z).right.frequency
    (N.crossFamily a b m h k z).leftFactor (N.crossFamily a b m h k z).rightFactor = _
  rw [crossFamily_leftFactor, crossFamily_rightFactor]
  apply Units.ext
  simp only [crossFamily, withLeaves, ratio, familyRatioConstant, Units.val_div_eq_div_val,
    Units.val_mul, Units.val_pow_eq_pow_val]
  field_simp

theorem crossFamily_left_chart (N : NodeInput F 1) (a b : Bool) (m h k z : Fˣ)
    (hp : (N.crossFamily a b m h k z).pivot ≠ 0) :
    Ostmann.FiniteField.pairMobiusValue (N.familyRoot m) (N.familyRatioConstant m h/z^2) =
      ((N.crossFamily a b m h k z).leftArgument hp:F) := by
  have he := (pair_coordinates_left (N.crossFamily a b m h k z) hp).1
  rw [crossFamily_argument, crossFamily_ratio] at he
  simpa only [Ostmann.FiniteField.pairFirst, Ostmann.FiniteField.pairMobiusValue,
    Units.val_one, one_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] using he

theorem crossFamily_right_chart (N : NodeInput F 1) (a b : Bool) (m h k z : Fˣ)
    (hp : (N.crossFamily a b m h k z).pivot ≠ 0) :
    Ostmann.FiniteField.pairMobiusValue (N.familyRoot m) (N.familyRatioConstant m h/z^2) -
      (N.familyRoot m:F) = ((N.crossFamily a b m h k z).rightArgument hp:F) := by
  rw [crossFamily_left_chart N a b m h k z hp]
  have he := crossFamily_difference N a b m h k z hp
  linear_combination he

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI
