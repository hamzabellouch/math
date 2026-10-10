import OAI.Geometry.EinsteinFour.WeylLaplacian
import OAI.Geometry.EinsteinFour.AngularCurvature

namespace OAI

/-! Quaternion contractions in the derivative-slot Green formula. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi Angular

noncomputable section

/-- Curvature coefficients with the final two slots in covector order. -/
def blockCoefficient (Q : Fin 3 → Geometry.Mat4) (t : Fin 3 → ℝ)
    (i k j l : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, t s * Q s i k * Q s j l

def plusCoefficient := blockCoefficient quaternionMatrix

def minusCoefficient := blockCoefficient oppositeMatrix

def einsteinCoefficient (t u : Fin 3 → ℝ) (i k j l : Fin 4) : ℝ :=
  plusCoefficient (fun s => 1 + t s) i k j l +
    minusCoefficient (fun s => 1 + u s) i k j l

/-- These coefficients are the actual Einstein curvature decomposition,
with the last two entries reversed to act on a covector slot. -/
theorem einsteinCoefficient_eq_tensor (t u : Fin 3 → ℝ) (i k j l : Fin 4) :
    einsteinCoefficient t u i k j l =
      einsteinCurvatureTensor (Matrix.diagonal t) (Matrix.diagonal u) i k l j := by
  have hb (a : Fin 3 → ℝ) (Q : Fin 3 → Geometry.Mat4) :
      blockTensor (1 + Matrix.diagonal a) Q i k l j =
        blockCoefficient Q (fun s => 1 + a s) i k j l := by
    simp [blockTensor, twoFormProduct, blockCoefficient, Matrix.add_apply,
      Matrix.one_apply, Matrix.diagonal_apply, add_mul, mul_add, Finset.sum_add_distrib,
      mul_assoc]
  simp only [einsteinCoefficient, einsteinCurvatureTensor, Pi.add_apply, hb,
    plusCoefficient, minusCoefficient]

/-- Orthogonality includes the normalization of the curvature two-forms. -/
theorem plus_twoForm_pairing (s r : Fin 3) :
    (∑ i, ∑ k, quaternionMatrix s i k * quaternionMatrix r i k) =
      if s = r then (4 : ℝ) else 0 := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases r <;> norm_num [TraceHessian.quaternionMatrix]

theorem opposite_twoForm_pairing (s r : Fin 3) :
    (∑ i, ∑ k, oppositeMatrix s i k * oppositeMatrix r i k) =
      if s = r then (4 : ℝ) else 0 := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases r <;> norm_num [oppositeMatrix, Geometry.oppositeQuaternion, TraceHessian.quaternionMatrix]

theorem mixed_twoForm_pairing (s r : Fin 3) :
    (∑ i, ∑ k, quaternionMatrix s i k * oppositeMatrix r i k) = 0 := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases r <;>
    norm_num [TraceHessian.quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion]

private theorem block_pairing (Q P : Fin 3 → Geometry.Mat4)
    (a b : Fin 3 → ℝ) (j l h n : Fin 4) :
    (∑ i, ∑ k, blockCoefficient Q a i k j l * blockCoefficient P b i k h n) =
      (1 / 4 : ℝ) * ∑ s, ∑ r, a s * b r * Q s j l * P r h n *
        (∑ i, ∑ k, Q s i k * P r i k) := by
  simp only [blockCoefficient, Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ k, ∑ s, ∑ r,
        (1 / 4 : ℝ) * a s * b r * Q s j l * P r h n *
          (Q s i k * P r i k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      calc
        _ = ∑ i, ∑ s, ∑ k, ∑ r,
            (1 / 4 : ℝ) * a s * b r * Q s j l * P r h n *
              (Q s i k * P r i k) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = ∑ s, ∑ i, ∑ k, ∑ r,
            (1 / 4 : ℝ) * a s * b r * Q s j l * P r h n *
              (Q s i k * P r i k) := Finset.sum_comm
        _ = ∑ s, ∑ i, ∑ r, ∑ k,
            (1 / 4 : ℝ) * a s * b r * Q s j l * P r h n *
              (Q s i k * P r i k) := by
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = ∑ s, ∑ r, ∑ i, ∑ k,
            (1 / 4 : ℝ) * a s * b r * Q s j l * P r h n *
              (Q s i k * P r i k) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_comm]
        _ = _ := by simp only [mul_assoc]

/-- Contracting two self-dual curvature blocks retains the product of their
three eigenvalues, with no missing two-form normalization. -/
theorem plus_block_pairing (a b : Fin 3 → ℝ) (j l h n : Fin 4) :
    (∑ i, ∑ k, plusCoefficient a i k j l * plusCoefficient b i k h n) =
      ∑ s, a s * b s * quaternionMatrix s j l * quaternionMatrix s h n := by
  simp only [plusCoefficient]
  rw [block_pairing]
  simp only [plus_twoForm_pairing, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The mixed block contraction is zero before pairing against any tensor. -/
theorem mixed_block_pairing (a b : Fin 3 → ℝ) (j l h n : Fin 4) :
    (∑ i, ∑ k, plusCoefficient a i k j l * minusCoefficient b i k h n) = 0 := by
  simp only [plusCoefficient, minusCoefficient]
  rw [block_pairing]
  simp only [mixed_twoForm_pairing, mul_zero, Finset.sum_const_zero]

private theorem block_oneForm_pairing (Q P : Fin 3 → Geometry.Mat4)
    (a : Fin 3 → ℝ) (s : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, blockCoefficient Q a i k j l * P s i k) =
      (1 / 2 : ℝ) * ∑ r, a r * Q r j l * (∑ i, ∑ k, Q r i k * P s i k) := by
  simp only [blockCoefficient, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ k, ∑ r, (1 / 2 : ℝ) * a r * Q r j l * (Q r i k * P s i k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ i, ∑ r, ∑ k, (1 / 2 : ℝ) * a r * Q r j l * (Q r i k * P s i k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ i, ∑ k, (1 / 2 : ℝ) * a r * Q r j l * (Q r i k * P s i k) :=
      Finset.sum_comm
    _ = _ := by simp only [mul_assoc]

/-- The matrix-slot curvature contraction retains precisely the matching
self-dual generator. -/
theorem plus_oneForm_pairing (a : Fin 3 → ℝ) (s : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, plusCoefficient a i k j l * quaternionMatrix s i k) =
      2 * a s * quaternionMatrix s j l := by
  simp only [plusCoefficient]
  rw [block_oneForm_pairing]
  simp only [plus_twoForm_pairing, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- The anti-self-dual curvature has no matrix-slot action on a plus Weyl
block: the two-form contraction vanishes before any Bianchi constraint. -/
theorem minus_oneForm_pairing (a : Fin 3 → ℝ) (s : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, minusCoefficient a i k j l * quaternionMatrix s i k) = 0 := by
  have hp (r : Fin 3) : (∑ i, ∑ k, oppositeMatrix r i k * quaternionMatrix s i k) = 0 := by
    simpa only [mul_comm] using mixed_twoForm_pairing s r
  simp only [minusCoefficient]
  rw [block_oneForm_pairing]
  simp only [hp, mul_zero, Finset.sum_const_zero]

private theorem opposite_column_pairing (s : Fin 3) (l h : Fin 4) :
    (∑ j, oppositeMatrix s j l * oppositeMatrix s j h) =
      if l = h then (1 : ℝ) else 0 := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases l <;> fin_cases h <;>
    norm_num [oppositeMatrix, Geometry.oppositeQuaternion, TraceHessian.quaternionMatrix]

theorem minus_block_pairing (a b : Fin 3 → ℝ) (j l h n : Fin 4) :
    (∑ i, ∑ k, minusCoefficient a i k j l * minusCoefficient b i k h n) =
      ∑ s, a s * b s * oppositeMatrix s j l * oppositeMatrix s h n := by
  simp only [minusCoefficient]
  rw [block_pairing]
  simp only [opposite_twoForm_pairing, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem minus_plus_block_pairing (a b : Fin 3 → ℝ) (j l h n : Fin 4) :
    (∑ i, ∑ k, minusCoefficient a i k j l * plusCoefficient b i k h n) = 0 := by
  calc
    _ = ∑ i, ∑ k, plusCoefficient b i k h n * minusCoefficient a i k j l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = 0 := mixed_block_pairing b a h n j l

private theorem quaternion_column_pairing (s : Fin 3) (l h : Fin 4) :
    (∑ j, quaternionMatrix s j l * quaternionMatrix s j h) =
      if l = h then (1 : ℝ) else 0 := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases l <;> fin_cases h <;>
    norm_num [TraceHessian.quaternionMatrix]

/-- The derivative-slot Ricci contraction contributes `3*v^2` when
`sum t_s^2 = 6*v^2`. -/
theorem plus_ricci_contraction (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (l h : Fin 4) :
    (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
      plusCoefficient t i k j l * einsteinCoefficient t u i k j h) =
        ((∑ s, t s ^ 2) / 2) * (if l = h then 1 else 0) := by
  have hinner (j : Fin 4) : (∑ i, ∑ k,
      plusCoefficient t i k j l * einsteinCoefficient t u i k j h) =
      ∑ s, t s * (1 + t s) * quaternionMatrix s j l * quaternionMatrix s j h := by
    simp only [einsteinCoefficient, mul_add, Finset.sum_add_distrib]
    rw [plus_block_pairing, mixed_block_pairing, add_zero]
    simp only [mul_add]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  simp only [mul_assoc]
  simp_rw [← Finset.mul_sum, quaternion_column_pairing]
  have he : (∑ s, t s * (1 + t s)) = ∑ s, t s ^ 2 := by
    calc
      _ = (∑ s, t s) + ∑ s, t s ^ 2 := by
        simp only [mul_add, mul_one, pow_two, Finset.sum_add_distrib]
      _ = _ := by rw [ht, zero_add]
  simp only [← mul_assoc, ← Finset.sum_mul, he]
  ring

/-- The anti-self-dual block has the same derivative-slot Ricci term. -/
theorem minus_ricci_contraction (t u : Fin 3 → ℝ) (hu : ∑ s, u s = 0)
    (l h : Fin 4) :
    (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
      minusCoefficient u i k j l * einsteinCoefficient t u i k j h) =
        ((∑ s, u s ^ 2) / 2) * (if l = h then 1 else 0) := by
  have hinner (j : Fin 4) : (∑ i, ∑ k,
      minusCoefficient u i k j l * einsteinCoefficient t u i k j h) =
      ∑ s, u s * (1 + u s) * oppositeMatrix s j l * oppositeMatrix s j h := by
    simp only [einsteinCoefficient, mul_add, Finset.sum_add_distrib]
    rw [minus_plus_block_pairing, minus_block_pairing, zero_add]
    simp only [mul_add]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  simp only [mul_assoc]
  simp_rw [← Finset.mul_sum, opposite_column_pairing]
  have he : (∑ s, u s * (1 + u s)) = ∑ s, u s ^ 2 := by
    calc
      _ = (∑ s, u s) + ∑ s, u s ^ 2 := by
        simp only [mul_add, mul_one, pow_two, Finset.sum_add_distrib]
      _ = _ := by rw [hu, zero_add]
  simp only [← mul_assoc, ← Finset.sum_mul, he]
  ring

/-- Total Bianchi coupling, used for the scalar part of the squared block. -/
theorem sum_mixedCouplingForm (Z : Tensor) (hb : Z.bianchi) :
    (∑ s, mixedCouplingForm s Z) = -4 * Z.squaredNorm := by
  calc
    _ = ∑ a, ∑ b, inner ℝ (gradientCoupling Z a b) (Z.matrix a b) := by
      simp only [mixedCouplingForm, gradientCoupling, sum_inner]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [gradientCoupling_eq Z hb, real_inner_smul_left,
        real_inner_self_eq_norm_sq, ← Finset.mul_sum, Tensor.squaredNorm]

/-- The matrix-slot part of the commutator plus its derivative-slot Ricci
part gives exactly the polynomial in equation (11). -/
theorem plus_commutator_scalar (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    ((∑ s, t s ^ 2) / 2) * Z.squaredNorm -
      (1 / 2 : ℝ) * (∑ s, t s * (1 + t s) * mixedCouplingForm s Z) =
        (7 / 6 : ℝ) * (∑ s, t s ^ 2) * Z.squaredNorm -
          4 * diagonalGradientForm t Z -
          4 * diagonalGradientForm (fun s => t s ^ 2 - (∑ r, t r ^ 2) / 3) Z := by
  let n := fun s => t s ^ 2 - (∑ r, t r ^ 2) / 3
  have hn : ∑ s, n s = 0 := by
    simp only [n, Fin.sum_univ_three]
    ring
  have he : (∑ s, t s * (1 + t s) * mixedCouplingForm s Z) =
      (∑ s, t s * mixedCouplingForm s Z) +
      (∑ s, n s * mixedCouplingForm s Z) +
      ((∑ r, t r ^ 2) / 3) * (∑ s, mixedCouplingForm s Z) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    dsimp [n]
    ring
  rw [he, weighted_mixedCouplingForm t ht Z hz hb,
    weighted_mixedCouplingForm n hn Z hz hb, sum_mixedCouplingForm Z hb]
  dsimp [n]
  ring

end

end PositiveEinsteinFour.CurvatureContraction

end OAI
