import OAI.NumberTheory.Ostmann.Tree.QuartetFactorRatios
import OAI.NumberTheory.Ostmann.Tree.QuartetFamily

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
variable {F : Type*} [Field F]

def modeMultiplier (bad : Bool) (d e : Fˣ) : Fˣ := if bad then e⁻¹ else d

namespace NodeInput
variable {d : ℕ}

theorem leftNode_leaves (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.leftNode hp).leaves = Density.left N.leaves := by
  cases he : N.left
  simp only [leftNode, he]

theorem rightNode_leaves (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.rightNode hp).leaves = Density.right N.leaves := by
  cases he : N.right
  simp only [rightNode, he]

def leftLambda (N : NodeInput F 1) (m : Fˣ) (bad : Bool) : Fˣ :=
  if bad then sharedCoefficient N.left N.D *
    (N.left.frequency*N.right.frequency/(N.s*N.D*N.u^2))*N.familyRoot m
  else residualCoefficient N.left N.D N.Xleft

def rightLambda (N : NodeInput F 1) (m : Fˣ) (bad : Bool) : Fˣ :=
  if bad then sharedCoefficient N.right N.D *
    (N.left.frequency*N.right.frequency/(N.s*N.D*N.u^2))*N.familyRoot m
  else residualCoefficient N.right N.D N.Xright

theorem crossFamily_left_parameter (N : NodeInput F 1) (hcons : N.parameters.consistent)
    (a b : Bool) (m h k z : Fˣ) (hp : (N.crossFamily a b m h k z).pivot ≠ 0) :
    ((N.crossFamily a b m h k z).leftNode hp).factorRatio a =
      (N.leftLambda m a*h^2) * modeMultiplier a
        ((N.crossFamily a b m h k z).leftArgument hp)
        ((N.crossFamily a b m h k z).rightArgument hp) := by
  have hc : N.left.childConsistent (N.u*N.a) := hcons.1
  cases a
  · let Q := N.crossFamily false b m h k z
    have hheld : Parameters.leafProduct (Density.right (Q.leftNode hp).leaves)=h := by
      rw [leftNode_leaves]
      simp only [Q, crossFamily, withLeaves, crossAssignment, Density.left_join,
        pairAssignment, Bool.false_eq_true, ↓reduceIte, Density.right_join, leafProduct_const_zero]
    have he := left_friendly_factor Q hp hc
    rw [hheld] at he
    exact he
  · let Q := N.crossFamily true b m h k z
    have hheld : Parameters.leafProduct (Density.left (Q.leftNode hp).leaves)=h := by
      rw [leftNode_leaves]
      simp only [Q, crossFamily, withLeaves, crossAssignment, Density.left_join,
        pairAssignment, ↓reduceIte, Density.left_join, leafProduct_const_zero]
    have he := left_bad_factor Q hp hc
    rw [hheld, show Q.argument=N.familyRoot m from crossFamily_argument N true b m h k z] at he
    rw [he]
    simp only [Q, crossFamily, withLeaves, leftLambda, modeMultiplier, ↓reduceIte]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem crossFamily_right_parameter (N : NodeInput F 1) (hcons : N.parameters.consistent)
    (a b : Bool) (m h k z : Fˣ) (hp : (N.crossFamily a b m h k z).pivot ≠ 0) :
    ((N.crossFamily a b m h k z).rightNode hp).factorRatio b =
      (N.rightLambda m b*k^2) * modeMultiplier b
        ((N.crossFamily a b m h k z).rightArgument hp)
        ((N.crossFamily a b m h k z).leftArgument hp) := by
  have hc : N.right.childConsistent (N.u*N.b) := hcons.2.1
  cases b
  · let Q := N.crossFamily a false m h k z
    have hheld : Parameters.leafProduct (Density.right (Q.rightNode hp).leaves)=k := by
      rw [rightNode_leaves]
      simp only [Q, crossFamily, withLeaves, crossAssignment, Density.right_join,
        pairAssignment, Bool.false_eq_true, ↓reduceIte, Density.right_join, leafProduct_const_zero]
    have he := right_friendly_factor Q hp hc
    rw [hheld] at he
    exact he
  · let Q := N.crossFamily a true m h k z
    have hheld : Parameters.leafProduct (Density.left (Q.rightNode hp).leaves)=k := by
      rw [rightNode_leaves]
      simp only [Q, crossFamily, withLeaves, crossAssignment, Density.right_join,
        pairAssignment, ↓reduceIte, Density.left_join, leafProduct_const_zero]
    have he := right_bad_factor Q hp hc
    rw [hheld, show Q.argument=N.familyRoot m from crossFamily_argument N a true m h k z] at he
    rw [he]
    simp only [Q, crossFamily, withLeaves, rightLambda, modeMultiplier, ↓reduceIte]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI
