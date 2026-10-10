import OAI.NumberTheory.Ostmann.Tree.QuartetZero

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
variable {F : Type*} [Field F]

def residualCoefficient {d : ℕ} (P : Parameters F (d+1)) (D X : Fˣ) : Fˣ :=
  match P with | .branch s _ b _ L R => (D*L.frequency/(R.frequency*s))*(X*b)^2

def sharedCoefficient {d : ℕ} (P : Parameters F (d+1)) (D : Fˣ) : Fˣ :=
  match P with | .branch s a _ _ L R => (D*R.frequency/(L.frequency*s))*a^2

namespace NodeInput
variable {d : ℕ}

theorem factor_residual_ratio (N : NodeInput F d) :
    N.factorRatio false = residualCoefficient N.parameters N.D N.Xright *
      (Parameters.leafProduct (Density.right N.leaves))^2*N.argument := by
  change ratio N.left.frequency N.right.frequency N.leftFactor N.rightFactor = _
  rw [argument_eq]
  apply Units.ext
  simp only [ratio, root, residualCoefficient,
    parameters, leftFactor, rightFactor, Units.val_div_eq_div_val, Units.val_mul,
    Units.val_pow_eq_pow_val]
  field_simp

theorem factor_shared_ratio (N : NodeInput F d) :
    N.factorRatio true = sharedCoefficient N.parameters N.D *
      (Parameters.leafProduct (Density.left N.leaves))^2*N.Xleft^2*N.argument := by
  change ratio N.right.frequency N.left.frequency N.rightFactor N.leftFactor = _
  rw [argument_eq]
  apply Units.ext
  simp only [ratio, root, sharedCoefficient,
    parameters, leftFactor, rightFactor, Units.val_div_eq_div_val, Units.val_mul,
    Units.val_pow_eq_pow_val]
  field_simp

theorem leftNode_parameters (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.leftNode hp).parameters = N.left := by
  cases he : N.left
  simp only [leftNode, he, parameters]

theorem rightNode_parameters (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.rightNode hp).parameters = N.right := by
  cases he : N.right
  simp only [rightNode, he, parameters]

theorem leftNode_D (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.leftNode hp).D = N.D := by
  cases he : N.left
  simp only [leftNode, he]

theorem rightNode_D (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.rightNode hp).D = N.D := by
  cases he : N.right
  simp only [rightNode, he]

theorem leftNode_residual (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.leftNode hp).Xright = N.Xleft := by
  cases he : N.left
  simp only [leftNode, he]

theorem rightNode_residual (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0) :
    (N.rightNode hp).Xright = N.Xright := by
  cases he : N.right
  simp only [rightNode, he]

theorem left_friendly_factor (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0)
    (hc : N.left.childConsistent (N.u*N.a)) :
    (N.leftNode hp).factorRatio false = residualCoefficient N.left N.D N.Xleft *
      (Parameters.leafProduct (Density.right (N.leftNode hp).leaves))^2*N.leftArgument hp := by
  rw [factor_residual_ratio, leftNode_parameters, leftNode_D, leftNode_residual,
    leftNode_argument N hp hc]

theorem right_friendly_factor (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0)
    (hc : N.right.childConsistent (N.u*N.b)) :
    (N.rightNode hp).factorRatio false = residualCoefficient N.right N.D N.Xright *
      (Parameters.leafProduct (Density.right (N.rightNode hp).leaves))^2*N.rightArgument hp := by
  rw [factor_residual_ratio, rightNode_parameters, rightNode_D, rightNode_residual,
    rightNode_argument N hp hc]

theorem left_bad_factor (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0)
    (hc : N.left.childConsistent (N.u*N.a)) :
    (N.leftNode hp).factorRatio true = sharedCoefficient N.left N.D *
      (Parameters.leafProduct (Density.left (N.leftNode hp).leaves))^2 *
      (N.left.frequency*N.right.frequency/(N.s*N.D*N.u^2))*N.argument/N.rightArgument hp := by
  rw [factor_shared_ratio, leftNode_parameters, leftNode_D, leftNode_shared,
    actual_shared_pivot_square, leftNode_argument N hp hc]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem right_bad_factor (N : NodeInput F (d+1)) (hp : N.pivot ≠ 0)
    (hc : N.right.childConsistent (N.u*N.b)) :
    (N.rightNode hp).factorRatio true = sharedCoefficient N.right N.D *
      (Parameters.leafProduct (Density.left (N.rightNode hp).leaves))^2 *
      (N.left.frequency*N.right.frequency/(N.s*N.D*N.u^2))*N.argument/N.leftArgument hp := by
  rw [factor_shared_ratio, rightNode_parameters, rightNode_D, rightNode_shared,
    actual_shared_pivot_square, rightNode_argument N hp hc]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI
