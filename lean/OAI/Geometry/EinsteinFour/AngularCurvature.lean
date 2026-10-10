import OAI.Geometry.EinsteinFour.AngularNormal

namespace OAI

/-! The normal Jacobi form of the actual quaternion curvature decomposition. -/

namespace PositiveEinsteinFour.Angular

open Matrix TraceHessian

noncomputable section

abbrev CurvatureArray := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

def normalVector (q : Directions) (i : Fin 3) (a : Fin 4) : ℝ :=
  ∑ b, quaternionMatrix i a b * q.val b

def twoFormNormal (Q : Mat4) (q : Directions) (i : Fin 3) : ℝ :=
  ∑ a, ∑ b, Q a b * normalVector q i a * q.val b

theorem twoFormNormal_plus (q : Directions) (i s : Fin 3) :
    twoFormNormal (quaternionMatrix s) q i = if i = s then 1 else 0 := by
  calc
    _ = (∑ a, q.val a ^ 2) * (if i = s then 1 else 0) := by
      fin_cases i <;> fin_cases s <;>
        simp [twoFormNormal, normalVector, quaternionMatrix, Fin.sum_univ_succ]
      all_goals ring
    _ = _ := by rw [direction_sum_sq]; simp

theorem twoFormNormal_minus (q : Directions) (i s : Fin 3) :
    twoFormNormal (oppositeMatrix s) q i = mixing i s q := by
  simp only [mixing, quadratic, mixingCoefficient_eq_table]
  fin_cases i <;> fin_cases s <;>
    simp [twoFormNormal, normalVector, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, coefficientTable, Fin.sum_univ_succ]
  all_goals ring

/-- Evaluate `<R(I_i q,q)q,I_j q>` as a linear functional on four-tensors. -/
def normalEvaluation (q : Directions) (i j : Fin 3) : CurvatureArray →ₗ[ℝ] ℝ where
  toFun R := ∑ a, ∑ b, ∑ c, ∑ d,
    R a b c d * normalVector q i a * q.val b * q.val c * normalVector q j d
  map_add' R S := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r R := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

def twoFormProduct (P Q : Mat4) : CurvatureArray := fun a b c d => P a b * Q d c

theorem normalEvaluation_product (P Q : Mat4) (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (twoFormProduct P Q) =
      twoFormNormal P q i * twoFormNormal Q q j := by
  change (∑ a, ∑ b, ∑ c, ∑ d,
    P a b * Q d c * normalVector q i a * q.val b * q.val c * normalVector q j d) = _
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c,
        P a b * Q d c * normalVector q i a * q.val b * q.val c * normalVector q j d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [twoFormNormal]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro c _
      ring

def blockTensor (A : Mat3) (Q : Fin 3 → Mat4) : CurvatureArray :=
  (1 / 2 : ℝ) • ∑ s, ∑ t, A s t • twoFormProduct (Q s) (Q t)

theorem normalEvaluation_blockTensor (A : Mat3) (Q : Fin 3 → Mat4)
    (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (blockTensor A Q) =
      (1 / 2 : ℝ) * ∑ s, ∑ t,
        A s t * (twoFormNormal (Q s) q i * twoFormNormal (Q t) q j) := by
  simp only [blockTensor, map_smul, map_sum, smul_eq_mul, normalEvaluation_product]

/-- Ric=3g removes the off-diagonal curvature blocks. -/
def einsteinCurvatureTensor (T U : Mat3) : CurvatureArray :=
  blockTensor (1 + T) quaternionMatrix + blockTensor (1 + U) oppositeMatrix

/-- Curvature decomposition gives the normal matrix used by the Jacobi ODE. -/
theorem normalEvaluation_einstein (T U : Mat3) (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (einsteinCurvatureTensor T U) =
      (1 + normalDeviation T U q) i j := by
  rw [einsteinCurvatureTensor, map_add, normalEvaluation_blockTensor,
    normalEvaluation_blockTensor]
  simp_rw [twoFormNormal_plus, twoFormNormal_minus]
  have ho := congrArg (fun A : Mat3 => A i j) (mixing_orthogonal q)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, mixingMatrix] at ho
  have hm : (∑ s, ∑ t, U s t * (mixing i s q * mixing j t q)) =
      (∑ t, (∑ s, mixing i s q * U s t) * mixing j t q) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp only [Matrix.add_apply, Matrix.one_apply, normalDeviation,
    Matrix.smul_apply, smul_eq_mul, rotated, Matrix.mul_apply,
    Matrix.transpose_apply, mixingMatrix, add_mul, Finset.sum_add_distrib,
    mul_add, mul_ite, ite_mul, mul_zero, zero_mul, one_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [ho, hm]
  simp only [Matrix.one_apply]
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] <;> ring

end

end PositiveEinsteinFour.Angular

end OAI
