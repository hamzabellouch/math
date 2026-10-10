import OAI.NumberTheory.Ostmann.Tree.DensityAlgebra
import OAI.NumberTheory.Ostmann.Tree.PairCoordinates

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
variable {F : Type*} [Field F]

def root (s D Hl Hr : Fˣ) : Fˣ := s/(D*Hl*Hr)

def child (s D p u H : Fˣ) : Fˣ := s/(D*p*u*H)

def ratio (sf sh Hf Hh : Fˣ) : Fˣ := sf*Hh/(sh*Hf)

theorem child_ratio (sl sr D p u Hl Hr : Fˣ) :
    child sl D p u Hl / child sr D p u Hr = ratio sl sr Hl Hr := by
  apply Units.ext
  simp only [child, ratio, Units.val_div_eq_div_val, Units.val_mul]
  field_simp

theorem shared_pivot_square (s sl sr D p u Hl Hr : Fˣ) :
    p^2 = (sl*sr/(s*D*u^2)) * root s D Hl Hr /
      (child sl D p u Hl * child sr D p u Hr) := by
  apply Units.ext
  simp only [child, root, Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val]
  field_simp

theorem held_square (s sf sh D Hf Hh : Fˣ) :
    ratio sf sh Hf Hh / root s D Hf Hh = (D*sf/(sh*s))*Hh^2 := by
  apply Units.ext
  simp only [ratio, root, Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val]
  field_simp

theorem root_swap (s D Hl Hr : Fˣ) : root s D Hr Hl = root s D Hl Hr := by
  simp [root, mul_comm, mul_left_comm]

theorem ratio_reciprocal_action (sf sh Hf Hh z : Fˣ) :
    ratio sf sh (Hf*z) (Hh/z) = ratio sf sh Hf Hh / z^2 := by
  simp [ratio, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]

theorem root_reciprocal_action (s D Hl Hr z : Fˣ) :
    root s D (Hl*z) (Hr/z) = root s D Hl Hr := by
  simp [root, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

structure NodeInput (F : Type*) [Field F] (depth : ℕ) where
  s : Fˣ
  a : Fˣ
  b : Fˣ
  u : Fˣ
  D : Fˣ
  Xleft : Fˣ
  Xright : Fˣ
  left : Parameters F depth
  right : Parameters F depth
  leaves : Leaves (depth+1) → Fˣ

namespace NodeInput
variable {d : ℕ}

def parameters (N : NodeInput F d) : Parameters F (d+1) :=
  .branch N.s N.a N.b N.u N.left N.right

def leftFactor (N : NodeInput F d) : Fˣ :=
  N.Xleft*N.a*Parameters.leafProduct (Density.left N.leaves)

def rightFactor (N : NodeInput F d) : Fˣ :=
  N.Xright*N.b*Parameters.leafProduct (Density.right N.leaves)

def pivot (N : NodeInput F d) : F :=
  Density.pivot N.s N.a N.b N.u N.left N.right N.Xleft N.Xright N.leaves

def pivotUnit (N : NodeInput F d) (hp : N.pivot ≠ 0) : Fˣ := Units.mk0 _ hp

def argument (N : NodeInput F d) : Fˣ :=
  Density.rootArgument N.parameters N.D N.Xleft N.Xright (N.a*N.b) N.leaves

def leftArgument (N : NodeInput F d) (hp : N.pivot ≠ 0) : Fˣ :=
  Density.rootArgument N.left N.D (N.pivotUnit hp) N.Xleft (N.u*N.a)
    (Density.left N.leaves)

def rightArgument (N : NodeInput F d) (hp : N.pivot ≠ 0) : Fˣ :=
  Density.rootArgument N.right N.D (N.pivotUnit hp) N.Xright (N.u*N.b)
    (Density.right N.leaves)

theorem argument_eq (N : NodeInput F d) :
    N.argument = root N.s N.D N.leftFactor N.rightFactor := by
  apply Units.ext
  simpa only [argument, parameters, root, leftFactor, rightFactor,
    Units.val_div_eq_div_val, Units.val_mul] using
    Density.branch_rootArgument N.s N.a N.b N.u N.D N.Xleft N.Xright
      N.left N.right N.leaves

theorem leftArgument_eq (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    N.leftArgument hp = child N.left.frequency N.D (N.pivotUnit hp) N.u N.leftFactor := by
  apply Units.ext
  simpa only [leftArgument, child, leftFactor, Units.val_div_eq_div_val, Units.val_mul] using
    Density.child_rootArgument N.left N.D (N.pivotUnit hp) N.Xleft N.u N.a
      (Density.left N.leaves)

theorem rightArgument_eq (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    N.rightArgument hp = child N.right.frequency N.D (N.pivotUnit hp) N.u N.rightFactor := by
  apply Units.ext
  simpa only [rightArgument, child, rightFactor, Units.val_div_eq_div_val, Units.val_mul] using
    Density.child_rootArgument N.right N.D (N.pivotUnit hp) N.Xright N.u N.b
      (Density.right N.leaves)

theorem argument_difference (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    (N.leftArgument hp : F) - (N.rightArgument hp : F) = (N.argument : F) := by
  exact Density.rootArgument_difference N.s N.a N.b N.u N.D N.Xleft N.Xright
    N.left N.right N.leaves hp

theorem actual_shared_pivot_square (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    (N.pivotUnit hp)^2 =
      (N.left.frequency*N.right.frequency/(N.s*N.D*N.u^2)) * N.argument /
        (N.leftArgument hp*N.rightArgument hp) := by
  rw [argument_eq, leftArgument_eq, rightArgument_eq]
  exact shared_pivot_square _ _ _ _ _ _ _ _

theorem actual_child_ratio (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    N.leftArgument hp / N.rightArgument hp =
      ratio N.left.frequency N.right.frequency N.leftFactor N.rightFactor := by
  rw [leftArgument_eq, rightArgument_eq]
  exact child_ratio _ _ _ _ _ _ _

theorem evaluate_eq (N : NodeInput F d) (hp : N.pivot ≠ 0) (g : F → ℂ) (incoming : F) :
    N.parameters.evaluate g N.D N.Xleft N.Xright incoming N.leaves =
      N.left.evaluate g N.D (N.pivotUnit hp) N.Xleft (N.leftArgument hp : F)
        (Density.left N.leaves) *
      N.right.evaluate g N.D (N.pivotUnit hp) N.Xright (N.rightArgument hp : F)
        (Density.right N.leaves) := by
  classical
  rw [leftArgument_eq, rightArgument_eq]
  change (if h : N.pivot=0 then 0 else
    N.left.evaluate g N.D (Units.mk0 N.pivot h) N.Xleft
      ((N.left.frequency:F)/((N.D:F)*(Units.mk0 N.pivot h:Fˣ)*N.u*N.leftFactor))
      (Density.left N.leaves) *
    N.right.evaluate g N.D (Units.mk0 N.pivot h) N.Xright
      ((N.right.frequency:F)/((N.D:F)*(Units.mk0 N.pivot h:Fˣ)*N.u*N.rightFactor))
      (Density.right N.leaves)) = _
  rw [dite_eq_right hp]
  simp only [pivotUnit, child, Units.val_div_eq_div_val, Units.val_mul]

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI
