import OAI.NumberTheory.Ostmann.Tree.QuartetCoordinates

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
variable {F : Type*} [Field F]

namespace NodeInput
variable {d : ℕ}

theorem actual_held_square_left (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    (N.leftArgument hp/N.rightArgument hp)/N.argument =
      (N.D*N.left.frequency/(N.right.frequency*N.s))*N.rightFactor^2 := by
  rw [actual_child_ratio, argument_eq]
  exact held_square _ _ _ _ _ _

theorem actual_held_square_right (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    (N.rightArgument hp/N.leftArgument hp)/N.argument =
      (N.D*N.right.frequency/(N.left.frequency*N.s))*N.leftFactor^2 := by
  rw [leftArgument_eq, rightArgument_eq, child_ratio, argument_eq, ← root_swap]
  exact held_square _ _ _ _ _ _

theorem residual_held_ratio (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    N.leftArgument hp/N.rightArgument hp =
      ((N.D*N.left.frequency/(N.right.frequency*N.s))*(N.Xright*N.b)^2) *
        (Parameters.leafProduct (Density.right N.leaves))^2 * N.argument := by
  have h := actual_held_square_left N hp
  apply div_eq_iff_eq_mul.mp at h
  rw [h]
  simp only [rightFactor, mul_pow]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem shared_held_ratio (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    N.rightArgument hp/N.leftArgument hp =
      ((N.D*N.right.frequency/(N.left.frequency*N.s))*N.a^2) *
        (Parameters.leafProduct (Density.left N.leaves))^2 * N.Xleft^2 * N.argument := by
  have h := actual_held_square_right N hp
  apply div_eq_iff_eq_mul.mp at h
  rw [h]
  simp only [leftFactor, mul_pow]
  ac_rfl

def leftNode (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) : NodeInput F d :=
  match N.left with
  | .branch s a b u L R =>
    ⟨s, a, b, u, N.D, N.pivotUnit hp, N.Xleft, L, R, Density.left N.leaves⟩

def rightNode (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) : NodeInput F d :=
  match N.right with
  | .branch s a b u L R =>
    ⟨s, a, b, u, N.D, N.pivotUnit hp, N.Xright, L, R, Density.right N.leaves⟩

theorem leftNode_argument (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0)
    (hc : N.left.childConsistent (N.u*N.a)) :
    (N.leftNode hp).argument = N.leftArgument hp := by
  cases he : N.left with
  | branch s a b u L R =>
    simp only [he, Parameters.childConsistent] at hc
    simp only [leftNode, he, argument, parameters, leftArgument]
    rw [hc]

theorem rightNode_argument (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0)
    (hc : N.right.childConsistent (N.u*N.b)) :
    (N.rightNode hp).argument = N.rightArgument hp := by
  cases he : N.right with
  | branch s a b u L R =>
    simp only [he, Parameters.childConsistent] at hc
    simp only [rightNode, he, argument, parameters, rightArgument]
    rw [hc]

theorem leftNode_shared (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.leftNode hp).Xleft = N.pivotUnit hp := by
  cases he : N.left; simp only [leftNode, he]

theorem rightNode_shared (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.rightNode hp).Xleft = N.pivotUnit hp := by
  cases he : N.right; simp only [rightNode, he]

theorem left_bad_ratio (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0)
    (hc : N.left.childConsistent (N.u*N.a))
    (hl : (N.leftNode hp).pivot ≠ 0) :
    (N.leftNode hp).rightArgument hl/(N.leftNode hp).leftArgument hl =
      (((N.leftNode hp).D*(N.leftNode hp).right.frequency /
          ((N.leftNode hp).left.frequency*(N.leftNode hp).s)) * (N.leftNode hp).a^2) *
        (Parameters.leafProduct (Density.left (N.leftNode hp).leaves))^2 *
        (N.left.frequency*N.right.frequency/(N.s*N.D*N.u^2)) * N.argument /
          N.rightArgument hp := by
  rw [shared_held_ratio, leftNode_shared, actual_shared_pivot_square,
    leftNode_argument N hp hc]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem right_bad_ratio (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0)
    (hc : N.right.childConsistent (N.u*N.b))
    (hr : (N.rightNode hp).pivot ≠ 0) :
    (N.rightNode hp).rightArgument hr/(N.rightNode hp).leftArgument hr =
      (((N.rightNode hp).D*(N.rightNode hp).right.frequency /
          ((N.rightNode hp).left.frequency*(N.rightNode hp).s)) * (N.rightNode hp).a^2) *
        (Parameters.leafProduct (Density.left (N.rightNode hp).leaves))^2 *
        (N.left.frequency*N.right.frequency/(N.s*N.D*N.u^2)) * N.argument /
          N.leftArgument hp := by
  rw [shared_held_ratio, rightNode_shared, actual_shared_pivot_square,
    rightNode_argument N hp hc]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI
