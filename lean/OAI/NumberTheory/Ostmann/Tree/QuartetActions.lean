import OAI.NumberTheory.Ostmann.Tree.QuartetCoordinates

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F]

def scaleLeaf (M : Leaves 0 → Fˣ) (z : Fˣ) : Leaves 0 → Fˣ := fun i => M i*z

theorem leafProduct_scaleLeaf (M : Leaves 0 → Fˣ) (z : Fˣ) :
    Parameters.leafProduct (scaleLeaf M z) = Parameters.leafProduct M*z := by
  simp [Parameters.leafProduct, scaleLeaf, Finset.prod_mul_distrib, Leaves]

def scalePair (M : Leaves 1 → Fˣ) (freeRight : Bool) (z : Fˣ) : Leaves 1 → Fˣ :=
  if freeRight then Density.join (Density.left M) (scaleLeaf (Density.right M) z)
  else Density.join (scaleLeaf (Density.left M) z) (Density.right M)

theorem leafProduct_scalePair (M : Leaves 1 → Fˣ) (side : Bool) (z : Fˣ) :
    Parameters.leafProduct (scalePair M side z) = Parameters.leafProduct M*z := by
  cases side <;>
    simp [scalePair, Density.leafProduct_split, Density.left_join, Density.right_join,
      leafProduct_scaleLeaf, mul_assoc, mul_left_comm, mul_comm]

def movePair (M : Leaves 1 → Fˣ) (z : Fˣ) : Leaves 1 → Fˣ :=
  Density.join (scaleLeaf (Density.left M) z) (scaleLeaf (Density.right M) z⁻¹)

theorem leafProduct_movePair (M : Leaves 1 → Fˣ) (z : Fˣ) :
    Parameters.leafProduct (movePair M z) = Parameters.leafProduct M := by
  simp [movePair, Density.leafProduct_split, Density.left_join, Density.right_join,
    leafProduct_scaleLeaf, mul_assoc, mul_left_comm, mul_comm]

def moveCross (M : Leaves 2 → Fˣ) (leftFreeRight rightFreeRight : Bool) (z : Fˣ) :
    Leaves 2 → Fˣ :=
  Density.join (scalePair (Density.left M) leftFreeRight z)
    (scalePair (Density.right M) rightFreeRight z⁻¹)

theorem leafProduct_moveCross (M : Leaves 2 → Fˣ) (a b : Bool) (z : Fˣ) :
    Parameters.leafProduct (moveCross M a b z) = Parameters.leafProduct M := by
  rw [moveCross, Density.leafProduct_split, Density.left_join, Density.right_join,
    leafProduct_scalePair, leafProduct_scalePair, Density.leafProduct_split M]
  simp [mul_assoc, mul_left_comm, mul_comm]

namespace NodeInput

def withLeaves {d : ℕ} (N : NodeInput F d) (M : Leaves (d+1) → Fˣ) : NodeInput F d :=
  { N with leaves := M }

theorem argument_withLeaves {d : ℕ} (N : NodeInput F d) (M : Leaves (d+1) → Fˣ)
    (hM : Parameters.leafProduct M = Parameters.leafProduct N.leaves) :
    (N.withLeaves M).argument = N.argument := by
  simp only [argument, parameters, withLeaves, Density.rootArgument, Parameters.frequency, hM]

theorem movePair_leftFactor (N : NodeInput F 0) (z : Fˣ) :
    (N.withLeaves (movePair N.leaves z)).leftFactor = N.leftFactor*z := by
  simp only [withLeaves, leftFactor, movePair, Density.left_join, leafProduct_scaleLeaf]
  simp only [mul_assoc]

theorem movePair_rightFactor (N : NodeInput F 0) (z : Fˣ) :
    (N.withLeaves (movePair N.leaves z)).rightFactor = N.rightFactor/z := by
  simp only [withLeaves, rightFactor, movePair, Density.right_join, leafProduct_scaleLeaf]
  simp only [div_eq_mul_inv, mul_assoc]

theorem movePair_ratio (N : NodeInput F 0) (z : Fˣ) (hp : N.pivot ≠ 0)
    (hq : (N.withLeaves (movePair N.leaves z)).pivot ≠ 0) :
    (N.withLeaves (movePair N.leaves z)).leftArgument hq /
      (N.withLeaves (movePair N.leaves z)).rightArgument hq =
      (N.leftArgument hp/N.rightArgument hp)/z^2 := by
  rw [actual_child_ratio, movePair_leftFactor, movePair_rightFactor,
    ratio_reciprocal_action, actual_child_ratio]; rfl

theorem moveCross_leftFactor (N : NodeInput F 1) (a b : Bool) (z : Fˣ) :
    (N.withLeaves (moveCross N.leaves a b z)).leftFactor = N.leftFactor*z := by
  simp only [withLeaves, leftFactor, moveCross, Density.left_join, leafProduct_scalePair]
  simp only [mul_assoc]

theorem moveCross_rightFactor (N : NodeInput F 1) (a b : Bool) (z : Fˣ) :
    (N.withLeaves (moveCross N.leaves a b z)).rightFactor = N.rightFactor/z := by
  simp only [withLeaves, rightFactor, moveCross, Density.right_join, leafProduct_scalePair]
  simp only [div_eq_mul_inv, mul_assoc]

theorem moveCross_ratio (N : NodeInput F 1) (a b : Bool) (z : Fˣ)
    (hp : N.pivot ≠ 0) (hq : (N.withLeaves (moveCross N.leaves a b z)).pivot ≠ 0) :
    (N.withLeaves (moveCross N.leaves a b z)).leftArgument hq /
      (N.withLeaves (moveCross N.leaves a b z)).rightArgument hq =
      (N.leftArgument hp/N.rightArgument hp)/z^2 := by
  rw [actual_child_ratio, moveCross_leftFactor, moveCross_rightFactor,
    ratio_reciprocal_action, actual_child_ratio]; rfl

def moveSame (M : Leaves 2 → Fˣ) (rightPair : Bool) (z : Fˣ) : Leaves 2 → Fˣ :=
  if rightPair then Density.join (Density.left M) (movePair (Density.right M) z)
  else Density.join (movePair (Density.left M) z) (Density.right M)

theorem moveSame_factors (N : NodeInput F 1) (side : Bool) (z : Fˣ) :
    (N.withLeaves (moveSame N.leaves side z)).leftFactor = N.leftFactor ∧
      (N.withLeaves (moveSame N.leaves side z)).rightFactor = N.rightFactor := by
  cases side <;> simp [moveSame, withLeaves, leftFactor, rightFactor,
    Density.left_join, Density.right_join, leafProduct_movePair]

theorem moveSame_pivot (N : NodeInput F 1) (side : Bool) (z : Fˣ) :
    (N.withLeaves (moveSame N.leaves side z)).pivot = N.pivot := by
  change ((N.left.frequency:F)*((N.withLeaves (moveSame N.leaves side z)).rightFactor:F)-
    (N.right.frequency:F)*((N.withLeaves (moveSame N.leaves side z)).leftFactor:F)) /
    ((N.s:F)*N.u) = _
  rw [(moveSame_factors N side z).1, (moveSame_factors N side z).2]; rfl

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI
