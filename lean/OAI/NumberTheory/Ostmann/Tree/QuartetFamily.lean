import OAI.NumberTheory.Ostmann.Tree.QuartetActions
import OAI.NumberTheory.Ostmann.Tree.QuartetHeld

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F]

def pairAssignment (freeRight : Bool) (free held : Fˣ) : Leaves 1 → Fˣ :=
  if freeRight then Density.join (fun _ => held) (fun _ => free)
  else Density.join (fun _ => free) (fun _ => held)

theorem leafProduct_const_zero (x : Fˣ) :
    Parameters.leafProduct (fun _ : Leaves 0 => x) = x := by
  simp [Parameters.leafProduct, Leaves]

theorem leafProduct_pairAssignment (side : Bool) (free held : Fˣ) :
    Parameters.leafProduct (pairAssignment side free held) = free*held := by
  cases side <;>
    simp [pairAssignment, Density.leafProduct_split, Density.left_join, Density.right_join,
      leafProduct_const_zero, mul_comm]

def crossAssignment (leftFreeRight rightFreeRight : Bool)
    (total heldLeft heldRight coordinate : Fˣ) : Leaves 2 → Fˣ :=
  Density.join (pairAssignment leftFreeRight coordinate heldLeft)
    (pairAssignment rightFreeRight (total/(coordinate*heldLeft*heldRight)) heldRight)

theorem leftProduct_crossAssignment (a b : Bool) (m h k z : Fˣ) :
    Parameters.leafProduct (Density.left (crossAssignment a b m h k z)) = z*h := by
  simp only [crossAssignment, Density.left_join, leafProduct_pairAssignment]

theorem rightProduct_crossAssignment (a b : Bool) (m h k z : Fˣ) :
    Parameters.leafProduct (Density.right (crossAssignment a b m h k z)) = m/(z*h) := by
  simp only [crossAssignment, Density.right_join, leafProduct_pairAssignment]
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.val_mul]
  field_simp

theorem product_crossAssignment (a b : Bool) (m h k z : Fˣ) :
    Parameters.leafProduct (crossAssignment a b m h k z) = m := by
  rw [Density.leafProduct_split, leftProduct_crossAssignment, rightProduct_crossAssignment]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

namespace NodeInput

def familyRoot (N : NodeInput F 1) (total : Fˣ) : Fˣ :=
  N.s/(N.D*N.Xleft*N.Xright*(N.a*N.b)*total)

def familyRatioConstant (N : NodeInput F 1) (total heldLeft : Fˣ) : Fˣ :=
  N.left.frequency*(N.Xright*N.b)*total /
    (N.right.frequency*(N.Xleft*N.a)*heldLeft^2)

def crossFamily (N : NodeInput F 1) (a b : Bool) (m h k z : Fˣ) : NodeInput F 1 :=
  N.withLeaves (crossAssignment a b m h k z)

theorem crossFamily_argument (N : NodeInput F 1) (a b : Bool) (m h k z : Fˣ) :
    (N.crossFamily a b m h k z).argument = N.familyRoot m := by
  simp only [crossFamily, withLeaves, argument, parameters, Density.rootArgument,
    Parameters.frequency, product_crossAssignment, familyRoot]

theorem crossFamily_leftFactor (N : NodeInput F 1) (a b : Bool) (m h k z : Fˣ) :
    (N.crossFamily a b m h k z).leftFactor = N.Xleft*N.a*(z*h) := by
  simp only [crossFamily, withLeaves, leftFactor, leftProduct_crossAssignment]

theorem crossFamily_rightFactor (N : NodeInput F 1) (a b : Bool) (m h k z : Fˣ) :
    (N.crossFamily a b m h k z).rightFactor = N.Xright*N.b*(m/(z*h)) := by
  simp only [crossFamily, withLeaves, rightFactor, rightProduct_crossAssignment]

theorem crossFamily_ratio (N : NodeInput F 1) (a b : Bool) (m h k z : Fˣ)
    (hp : (N.crossFamily a b m h k z).pivot ≠ 0) :
    (N.crossFamily a b m h k z).leftArgument hp /
      (N.crossFamily a b m h k z).rightArgument hp = N.familyRatioConstant m h/z^2 := by
  rw [actual_child_ratio, crossFamily_leftFactor, crossFamily_rightFactor]
  apply Units.ext
  simp only [crossFamily, withLeaves, ratio, familyRatioConstant, Units.val_div_eq_div_val,
    Units.val_mul, Units.val_pow_eq_pow_val]
  field_simp

theorem crossFamily_difference (N : NodeInput F 1) (a b : Bool) (m h k z : Fˣ)
    (hp : (N.crossFamily a b m h k z).pivot ≠ 0) :
    ((N.crossFamily a b m h k z).leftArgument hp:F) -
      ((N.crossFamily a b m h k z).rightArgument hp:F) = (N.familyRoot m:F) := by
  rw [argument_difference, crossFamily_argument]

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI
