import OAI.Geometry.EinsteinFour.HighestProjection
import OAI.Geometry.EinsteinFour.GradientOperator

namespace OAI

/-! The actual real coupled operator used for the plus projection. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- A real outer vector tensored with an arbitrary matrix-valued four-vector. -/
def rawWeight (a : Vec) (Z : RawGradient) : Hessian := fun i j b c => a i * Z b c j

theorem rawWeight_add (a : Vec) (Z W : RawGradient) :
    rawWeight a (Z + W) = rawWeight a Z + rawWeight a W := by
  funext i j b c
  change a i * (Z b c j + W b c j) = a i * Z b c j + a i * W b c j
  ring

theorem rawWeight_smul (a : Vec) (r : ℝ) (Z : RawGradient) :
    rawWeight a (r • Z) = r • rawWeight a Z := by
  funext i j b c
  change a i * (r * Z b c j) = r * (a i * Z b c j)
  ring

/-- The total infinitesimal action obeys the product rule on an actual tensor. -/
theorem totalPlus_rawWeight (s : Fin 3) (a : Vec) (Z : RawGradient) :
    totalPlus s (rawWeight a Z) =
      rawWeight (quaternion s a) Z + rawWeight a (rawGradientGenerator s Z) := by
  funext i j b c
  change totalPlus s (rawWeight a Z) i j b c =
    quaternion s a i * Z b c j + a i * rawGradientGenerator s Z b c j
  have ha := quaternionMatrix_apply s a i
  have hZ := quaternionMatrix_apply s (Z b c) j
  simp only [Fin.sum_univ_four] at ha hZ
  simp [totalPlus, rawWeight, rawGradientGenerator, rawMatrixRotation,
    matrixAction, Fin.sum_univ_three, Fin.sum_univ_four]
  rw [← ha, ← hZ]
  ring

/-- The matrix kernel of `Σ I_outer,s (I_inner,s + Σ_s)`. -/
def couplingKernel (p q : TensorIndex) : ℝ := ∑ s : Fin 3,
  quaternionMatrix s p.1 q.1 *
    ((if p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2
        then quaternionMatrix s p.2.1 q.2.1 else 0) +
      (if p.2.1 = q.2.1 ∧ p.2.2.2 = q.2.2.2
        then rotation s p.2.2.1 q.2.2.1 else 0) +
      (if p.2.1 = q.2.1 ∧ p.2.2.1 = q.2.2.1
        then rotation s p.2.2.2 q.2.2.2 else 0))

def coupledOperator (X : Hessian) : Hessian := fun i j a b =>
  ∑ q : TensorIndex, couplingKernel (i, j, a, b) q * tensorCoordinates X q

@[simp] theorem coupledOperator_coordinates (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (coupledOperator X) p =
      ∑ q : TensorIndex, couplingKernel p q * tensorCoordinates X q := by
  rcases p with ⟨i, j, a, b⟩
  rfl

theorem couplingKernel_symmetric (p q : TensorIndex) :
    couplingKernel p q = couplingKernel q p := by
  unfold couplingKernel
  apply Finset.sum_congr rfl
  intro s _
  rw [quaternionMatrix_skew s p.1 q.1,
    quaternionMatrix_skew s p.2.1 q.2.1,
    rotation_skew s p.2.2.1 q.2.2.1,
    rotation_skew s p.2.2.2 q.2.2.2]
  simp only [eq_comm (a := q.2.1) (b := p.2.1),
    eq_comm (a := q.2.2.1) (b := p.2.2.1),
    eq_comm (a := q.2.2.2) (b := p.2.2.2)]
  split_ifs <;> ring

private theorem symmetric_matrix_pairing {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i) (x y : ι → ℝ) :
    (∑ i, (∑ j, A i j * x j) * y i) =
      ∑ i, x i * (∑ j, A i j * y j) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i]
  ring

theorem coupledOperator_selfadjoint (X Y : Hessian) :
    hessianPairing (coupledOperator X) Y = hessianPairing X (coupledOperator Y) := by
  have h := symmetric_matrix_pairing couplingKernel couplingKernel_symmetric
    (tensorCoordinates X) (tensorCoordinates Y)
  simp_rw [← coupledOperator_coordinates] at h
  rw [tensorCoordinates_pairing, tensorCoordinates_pairing] at h
  exact h

/-- Entrywise kernel reduction to the two actual slot actions. -/
theorem coupledOperator_apply (X : Hessian) (i j : Fin 4) (a b : Fin 3) :
    coupledOperator X i j a b = ∑ s : Fin 3, ∑ k : Fin 4,
      quaternionMatrix s i k * ((∑ l : Fin 4, quaternionMatrix s j l * X k l a b) +
        matrixAction s (X k j) a b) := by
  simp only [coupledOperator, couplingKernel, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp [Fintype.sum_prod_type, tensorCoordinates, matrixAction_row_sum,
    add_mul, mul_add, Finset.sum_add_distrib,
    ite_mul, mul_ite, ite_and, Finset.mul_sum]
  ring_nf

theorem coupledOperator_add (X Y : Hessian) :
    coupledOperator (X + Y) = coupledOperator X + coupledOperator Y := by
  funext i j a b
  change (∑ q : TensorIndex, couplingKernel (i,j,a,b) q *
    (tensorCoordinates X q + tensorCoordinates Y q)) =
      coupledOperator X i j a b + coupledOperator Y i j a b
  simp only [mul_add, Finset.sum_add_distrib, coupledOperator]

theorem coupledOperator_smul (r : ℝ) (X : Hessian) :
    coupledOperator (r • X) = r • coupledOperator X := by
  funext i j a b
  change (∑ q : TensorIndex, couplingKernel (i,j,a,b) q *
    (r * tensorCoordinates X q)) = r * _
  simp only [mul_left_comm, ← Finset.mul_sum, coupledOperator]

/-- The actual coupled operator on a real rank-one tensor. -/
theorem coupledOperator_rawWeight (a : Vec) (Z : RawGradient) :
    coupledOperator (rawWeight a Z) =
      ∑ s : Fin 3, rawWeight (quaternion s a) (rawGradientGenerator s Z) := by
  funext i j b c
  simp only [Fin.sum_univ_three, Pi.add_apply, Matrix.add_apply, rawWeight]
  change coupledOperator (rawWeight a Z) i j b c =
    quaternion 0 a i * rawGradientGenerator 0 Z b c j +
    quaternion 1 a i * rawGradientGenerator 1 Z b c j +
    quaternion 2 a i * rawGradientGenerator 2 Z b c j
  rw [coupledOperator_apply]
  have ha (s : Fin 3) := quaternionMatrix_apply s a i
  have hZ (s : Fin 3) := quaternionMatrix_apply s (Z b c) j
  simp only [Fin.sum_univ_four] at ha hZ
  simp [rawWeight, matrixAction, rawGradientGenerator, rawMatrixRotation,
    Fin.sum_univ_three, Fin.sum_univ_four]
  rw [← ha 0, ← ha 1, ← ha 2, ← hZ 0, ← hZ 1, ← hZ 2]
  ring

/-- The actual polynomial used for the total-plus spectral projection. -/
def plusPolynomial (X : Hessian) : Hessian :=
  (1 / 12 : ℝ) • ((7 : ℝ) • X - coupledOperator X)

end
end PositiveEinsteinFour.HighestHessian

end OAI
