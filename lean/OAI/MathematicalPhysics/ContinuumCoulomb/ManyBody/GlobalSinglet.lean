import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.Singlet
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.DiagonalPenalty
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Perturbation
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! Canonical singlet/triplet coordinates for simultaneous fresh mediator pairs. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace

section

theorem bellScale_atLeastTwo : Nat.AtLeastTwo (1 + 1) :=
  @Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)

attribute [local instance] bellScale_atLeastTwo

def bellScale : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)

end

theorem bellScale_sq : bellScale ^ 2 = (1 / 2 : ℂ) := by
  unfold bellScale
  rw [← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  norm_num

@[simp] theorem bellScale_star : star bellScale = bellScale := by
  simp [bellScale]

def bellRaw : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 1; 1, 0, 1, 0; -1, 0, 1, 0; 0, 1, 0, -1]

def bellMatrix : Matrix (Fin 4) (Fin 4) ℂ := bellScale • bellRaw

theorem bellRaw_gram : bellRaw.conjTranspose * bellRaw = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bellRaw, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem bellRaw_cogram : bellRaw * bellRaw.conjTranspose = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bellRaw, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem bellScale_twice_sq : bellScale * (bellScale * 2) = 1 := by
  calc
    _ = 2 * bellScale ^ 2 := by ring
    _ = 1 := by rw [bellScale_sq]; norm_num

theorem bellMatrix_gram : bellMatrix.conjTranspose * bellMatrix = 1 := by
  simp only [bellMatrix, Matrix.conjTranspose_smul, bellScale_star,
    smul_mul_assoc, mul_smul_comm, bellRaw_gram, smul_smul, bellScale_twice_sq, one_smul]

theorem bellMatrix_cogram : bellMatrix * bellMatrix.conjTranspose = 1 := by
  simp only [bellMatrix, Matrix.conjTranspose_smul, bellScale_star,
    smul_mul_assoc, mul_smul_comm, bellRaw_cogram, smul_smul, bellScale_twice_sq, one_smul]

theorem bellMatrix_singlet (i : Fin 4) : bellMatrix i 0 = bellScale * spinSinglet i := by
  fin_cases i <;> simp [bellMatrix, bellRaw, spinSinglet]

theorem bellRaw_heisenberg : heisenberg * bellRaw =
    bellRaw * Matrix.diagonal (fun a : Fin 4 => if a = 0 then (-3 : ℂ) else 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bellRaw, heisenberg, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ]

theorem bellMatrix_heisenberg : heisenberg * bellMatrix =
    bellMatrix * Matrix.diagonal (fun a : Fin 4 => if a = 0 then (-3 : ℂ) else 1) := by
  simp only [bellMatrix, mul_smul_comm, smul_mul_assoc, bellRaw_heisenberg]

def bellTransform (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  bellMatrix.conjTranspose * M * bellMatrix

theorem bellTransform_mul (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    bellTransform M * bellTransform N = bellTransform (M * N) := by
  unfold bellTransform
  calc
    _ = bellMatrix.conjTranspose * M * (bellMatrix * bellMatrix.conjTranspose) * N * bellMatrix := by
      simp only [mul_assoc]
    _ = _ := by rw [bellMatrix_cogram]; simp only [mul_one, mul_assoc]

/-- The transformed zero coordinate is the actual normalized singlet
matrix element, including the normalization factor one half. -/
theorem bellTransform_zero_zero (M : Matrix (Fin 4) (Fin 4) ℂ) :
    bellTransform M 0 0 = (1 / 2 : ℂ) * singletMatrixElement M := by
  unfold bellTransform
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, bellMatrix_singlet,
    star_mul, bellScale_star, Finset.sum_mul]
  have hpoint (i j : Fin 4) :
      star (spinSinglet i) * bellScale * M i j * (bellScale * spinSinglet j) =
        bellScale ^ 2 * (star (spinSinglet i) * M i j * spinSinglet j) := by ring
  simp_rw [hpoint, bellScale_sq]
  unfold singletMatrixElement
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem bell_first_pauli_zero (μ : Fin 3) : bellTransform (firstPauli μ) 0 0 = 0 := by
  rw [bellTransform_zero_zero, singlet_first_pauli, mul_zero]

theorem bell_second_pauli_zero (μ : Fin 3) : bellTransform (secondPauli μ) 0 0 = 0 := by
  rw [bellTransform_zero_zero, singlet_second_pauli, mul_zero]

theorem bell_first_first_zero (μ ν : Fin 3) :
    (bellTransform (firstPauli μ) * bellTransform (firstPauli ν)) 0 0 =
      if μ = ν then 1 else 0 := by
  rw [bellTransform_mul, bellTransform_zero_zero, singlet_first_first]
  split_ifs <;> norm_num

theorem bell_first_second_zero (μ ν : Fin 3) :
    (bellTransform (firstPauli μ) * bellTransform (secondPauli ν)) 0 0 =
      if μ = ν then -1 else 0 := by
  rw [bellTransform_mul, bellTransform_zero_zero, singlet_first_second]
  split_ifs <;> norm_num

abbrev MediatorBasis (r : ℕ) := Fin r → Fin 4

def globalBellMatrix (r : ℕ) : Matrix (MediatorBasis r) (MediatorBasis r) ℂ :=
  fun a b => ∏ e, bellMatrix (a e) (b e)

theorem bell_column_inner (a b : Fin 4) :
    (∑ s, star (bellMatrix s a) * bellMatrix s b) = if a = b then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M a b) bellMatrix_gram
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

theorem bell_row_inner (a b : Fin 4) :
    (∑ s, bellMatrix a s * star (bellMatrix b s)) = if a = b then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M a b) bellMatrix_cogram
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

theorem product_delta (r : ℕ) (a b : MediatorBasis r) :
    (∏ e, if a e = b e then (1 : ℂ) else 0) = if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨e, he⟩ := Function.ne_iff.mp hab
    rw [ite_eq_right hab]
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

/-- The tensor product of all local Bell changes of coordinates is
unitary for every number of simultaneous mediators. -/
theorem globalBellMatrix_gram (r : ℕ) :
    (globalBellMatrix r).conjTranspose * globalBellMatrix r = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, globalBellMatrix,
    star_prod, ← Finset.prod_mul_distrib, Matrix.one_apply]
  rw [← Fintype.prod_sum (fun e s => star (bellMatrix s (a e)) * bellMatrix s (b e))]
  simp_rw [bell_column_inner]
  exact product_delta r a b

theorem globalBellMatrix_cogram (r : ℕ) :
    globalBellMatrix r * (globalBellMatrix r).conjTranspose = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, globalBellMatrix,
    star_prod, ← Finset.prod_mul_distrib, Matrix.one_apply]
  rw [← Fintype.prod_sum (fun e s => bellMatrix (a e) s * star (bellMatrix (b e) s))]
  simp_rw [bell_row_inner]
  exact product_delta r a b

def mediatorVacuum (r : ℕ) : MediatorBasis r := fun _ => 0

def mediatorExcitationNumber (r : ℕ) (a : MediatorBasis r) : ℕ :=
  (Finset.univ.filter (fun e => a e ≠ 0)).card

theorem mediatorExcitationNumber_pos (r : ℕ) (a : MediatorBasis r)
    (ha : a ≠ mediatorVacuum r) : 1 ≤ mediatorExcitationNumber r a := by
  obtain ⟨e, he⟩ := Function.ne_iff.mp ha
  exact Finset.card_pos.mpr ⟨e, by simpa [mediatorVacuum] using he⟩

def mediatorPenaltyWeight (r : ℕ) (Delta : ℝ) (a : MediatorBasis r) : ℝ :=
  4 * Delta * mediatorExcitationNumber r a

abbrev MediatorHighBasis (r : ℕ) := {a : MediatorBasis r // a ≠ mediatorVacuum r}

/-- The actual diagonal excitation penalty has gap four Delta and
its explicit inverse is bounded by the reciprocal gap. -/
theorem mediatorPenalty_inverse_data (r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta) :
    let weight : MediatorHighBasis r → ℝ := fun a => mediatorPenaltyWeight r Delta a.val
    (∀ x, diagonalPenalty weight (diagonalPenalty (fun a => (weight a)⁻¹) x) = x) ∧
      ‖diagonalPenalty (fun a => (weight a)⁻¹)‖ ≤ 1 / (4 * Delta) ∧
      (∀ x, (4 * Delta) * ‖x‖ ^ 2 ≤ ⟪x, diagonalPenalty weight x⟫_ℝ) := by
  intro weight
  have hg : 0 < 4 * Delta := by positivity
  have hgap (a : MediatorHighBasis r) : 4 * Delta ≤ weight a := by
    have ha : (1 : ℝ) ≤ mediatorExcitationNumber r a.val := by
      exact_mod_cast mediatorExcitationNumber_pos r a.val a.property
    simpa only [mul_one, weight, mediatorPenaltyWeight] using
      mul_le_mul_of_nonneg_left ha hg.le
  exact ⟨diagonalPenalty_inverse_right weight (fun a => ne_of_gt (hg.trans_le (hgap a))),
    diagonalPenalty_inverse_norm hg weight hgap, diagonalPenalty_gap weight (4 * Delta) hgap⟩

end ContinuumCoulomb

end

end OAI
