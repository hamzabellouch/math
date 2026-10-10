import OAI.Geometry.EinsteinFour.TraceAdjoint

namespace OAI

/-! Skew matrix actions on the actual four tensor slots. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

/-- The usual reindexing proof for a real skew-adjoint matrix. -/
theorem skew_matrix_pairing {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = -A j i) (x y : ι → ℝ) :
    (∑ i, (∑ j, A i j * x j) * y i) =
      -(∑ i, x i * (∑ j, A i j * y j)) := by
  calc
    _ = ∑ i, ∑ j, A i j * x j * y i := by simp_rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, A i j * x j * y i := Finset.sum_comm
    _ = ∑ j, -(∑ i, x j * (A j i * y i)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hA i j]
      ring
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [Finset.sum_neg_distrib]

abbrev TensorIndex := Fin 4 × Fin 4 × Fin 3 × Fin 3

def tensorCoordinates (X : Hessian) (p : TensorIndex) : ℝ :=
  X p.1 p.2.1 p.2.2.1 p.2.2.2

theorem tensorCoordinates_pairing (X Y : Hessian) :
    (∑ p : TensorIndex, tensorCoordinates X p * tensorCoordinates Y p) =
      hessianPairing X Y := by
  simp only [Fintype.sum_prod_type, tensorCoordinates, hessianPairing]
  calc
    _ = ∑ i : Fin 4, ∑ a : Fin 3, ∑ j : Fin 4, ∑ b : Fin 3,
        X i j a b * Y i j a b := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ a : Fin 3, ∑ i : Fin 4, ∑ j : Fin 4, ∑ b : Fin 3,
        X i j a b * Y i j a b := Finset.sum_comm
    _ = ∑ a : Fin 3, ∑ i : Fin 4, ∑ b : Fin 3, ∑ j : Fin 4,
        X i j a b * Y i j a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

/-- The Kronecker sum of the four actual infinitesimal rotation actions. -/
def plusKernel (s : Fin 3) (p q : TensorIndex) : ℝ :=
  (if p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
    then quaternionMatrix s p.1 q.1 else 0) +
  (if p.1 = q.1 ∧ p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
    then quaternionMatrix s p.2.1 q.2.1 else 0) +
  (if p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2.2 = q.2.2.2
    then rotation s p.2.2.1 q.2.2.1 else 0) +
  (if p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1
    then rotation s p.2.2.2 q.2.2.2 else 0)

theorem quaternionMatrix_skew (s : Fin 3) (i j : Fin 4) :
    quaternionMatrix s i j = -quaternionMatrix s j i := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;> norm_num [quaternionMatrix]

theorem rotation_skew (s : Fin 3) (i j : Fin 3) :
    rotation s i j = -rotation s j i := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;> norm_num [rotation]

theorem plusKernel_skew (s : Fin 3) (p q : TensorIndex) :
    plusKernel s p q = -plusKernel s q p := by
  unfold plusKernel
  rw [quaternionMatrix_skew s p.1 q.1,
    quaternionMatrix_skew s p.2.1 q.2.1,
    rotation_skew s p.2.2.1 q.2.2.1,
    rotation_skew s p.2.2.2 q.2.2.2]
  simp only [eq_comm (a := q.1) (b := p.1),
    eq_comm (a := q.2.1) (b := p.2.1),
    eq_comm (a := q.2.2.1) (b := p.2.2.1),
    eq_comm (a := q.2.2.2) (b := p.2.2.2)]
  split_ifs <;> ring

theorem matrixAction_row_sum (s : Fin 3) (M : Mat) (a b : Fin 3) :
    matrixAction s M a b = (∑ c, rotation s a c * M c b) +
      ∑ c, rotation s b c * M a c := by
  unfold matrixAction
  simp only [Finset.sum_sub_distrib]
  have h (c : Fin 3) : M a c * rotation s c b = -(rotation s b c * M a c) := by
    rw [rotation_skew s c b]
    ring
  simp_rw [h]
  rw [Finset.sum_neg_distrib]
  ring

theorem hessianPairing_add_left (X Y Z : Hessian) :
    hessianPairing (X + Y) Z = hessianPairing X Z + hessianPairing Y Z := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b + Y i j a b) * Z i j a b) = _
  simp only [add_mul, hessianPairing, Finset.sum_add_distrib]

theorem hessianPairing_smul_left (r : ℝ) (X Y : Hessian) :
    hessianPairing (r • X) Y = r * hessianPairing X Y := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (r * X i j a b) * Y i j a b) = _
  simp only [mul_assoc, hessianPairing, ← Finset.mul_sum]

/-- Matrix-slot Frobenius pairing. -/
def matrixPairing (M N : Mat) : ℝ := ∑ a, ∑ b, M a b * N a b

theorem matrixPairing_coordinates (a b c d e a' b' c' d' e' : ℝ) :
    matrixPairing (ofCoordinates a b c d e) (ofCoordinates a' b' c' d' e') =
      2 * a * a' + a * b' + b * a' + 2 * b * b' +
      2 * c * c' + 2 * d * d' + 2 * e * e' := by
  simp [matrixPairing, ofCoordinates, Fin.sum_univ_succ]
  ring

theorem matrixNormSq_coordinates (a b c d e : ℝ) :
    matrixNormSq (ofCoordinates a b c d e) =
      2 * (a ^ 2 + a * b + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  simp [matrixNormSq, ofCoordinates, Fin.sum_univ_succ]
  ring

theorem hessianPairing_derivative_order (X Y : Hessian) :
    hessianPairing X Y = ∑ i, ∑ j, matrixPairing (X i j) (Y i j) := by
  rw [← tensorCoordinates_pairing]
  simp only [Fintype.sum_prod_type, tensorCoordinates, matrixPairing]

theorem hessianNormSq_derivative_order (X : Hessian) :
    hessianNormSq X = ∑ i, ∑ j, matrixNormSq (X i j) := by
  rw [← hessianPairing_self, hessianPairing_derivative_order]
  simp only [matrixPairing, matrixNormSq, pow_two]

end
end PositiveEinsteinFour.TraceHessian

end OAI
