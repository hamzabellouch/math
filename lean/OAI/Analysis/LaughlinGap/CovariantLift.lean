import Mathlib
import OAI.Analysis.LaughlinGap.RealOccupation

namespace OAI

/-! Covariant Lift. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def lift (B : ι → Matrix κ κ ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ where
  toFun A := ∑ i, ∑ j, A i j • ((B i).transpose * B j)
  map_add' A C := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r A := by simp [Finset.smul_sum, smul_smul]

noncomputable def combination (B : ι → Matrix κ κ ℝ) :
    (ι → ℝ) →ₗ[ℝ] Matrix κ κ ℝ where
  toFun a := ∑ i, a i • B i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.smul_sum, smul_smul]

omit [DecidableEq ι] in
lemma lift_rankOne [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (x y : ι → ℝ) :
    lift B (Matrix.vecMulVec x y) = (combination B x).transpose * combination B y := by
  simp only [lift, combination, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply,
    Matrix.transpose_sum, Matrix.transpose_smul, Matrix.sum_mul, Matrix.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

omit [DecidableEq ι] [DecidableEq κ] in
lemma lift_transpose [DecidableEq ι] [DecidableEq κ]
    (B : ι → Matrix κ κ ℝ) (A : Matrix ι ι ℝ) :
    (lift B A).transpose = lift B A.transpose := by
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_sum,
    Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma lift_positive (B : ι → Matrix κ κ ℝ) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : (lift B A).PosSemidef := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have he : star C * C = ∑ k, Matrix.vecMulVec (fun i => C k i) (fun i => C k i) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
      Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [he, map_sum]
  apply Matrix.posSemidef_sum
  intro k hk
  rw [lift_rankOne]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (combination B (fun i => C k i))

omit [DecidableEq ι] in
lemma complexify_combination [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (a : ι → ℝ) :
    complexify (combination B a) = ∑ i, (a i : ℂ) • complexify (B i) := by
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  exact_mod_cast (rfl : a i • complexify (B i) = a i • complexify (B i))

omit [DecidableEq ι] in
lemma complexify_lift [DecidableEq ι] (B : ι → Matrix κ κ ℝ) (A : Matrix ι ι ℝ) :
    complexify (lift B A) = matrixLift (fun i => complexify (B i)) (A.map (algebraMap ℝ ℂ)) := by
  simp only [lift, matrixLift, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    map_mul, complexify_transpose, Matrix.map_apply]
  rfl

structure Covariant (L : Matrix κ κ ℝ) (D : Matrix ι ι ℝ)
    (B : ι → Matrix κ κ ℝ) : Prop where
  lower : ∀ i, commutator L (B i) = -∑ j, D i j • B j
  raise : ∀ i, commutator L.transpose (B i) = -∑ j, D j i • B j

lemma commutator_transpose (L A : Matrix κ κ ℝ) :
    commutator L A.transpose = -(commutator L.transpose A).transpose := by
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  abel

omit [DecidableEq ι] in
lemma Covariant.transpose [DecidableEq ι] {L : Matrix κ κ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L D B) :
    Covariant L.transpose D.transpose B where
  lower i := h.raise i
  raise i := by simpa using h.lower i

lemma Covariant.commutator_lift {L : Matrix κ κ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L D B) (A : Matrix ι ι ℝ) :
    commutator L (lift B A) = lift B (commutator D A) := by
  have ht (i : ι) : commutator L (B i).transpose = ∑ k, D k i • (B k).transpose := by
    rw [commutator_transpose, h.raise, Matrix.transpose_neg, neg_neg]
    simp only [Matrix.transpose_sum, Matrix.transpose_smul]
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [map_sum, map_smul, commutator_mul, ht, h.lower, Matrix.sum_mul,
    Matrix.mul_neg, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← sub_eq_add_neg, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
  simp only [Averaging.commutator, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply,
    Matrix.mul_apply, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]
  congr 1
  · conv_lhs =>
      rw [Finset.sum_comm]
      arg 2
      ext j
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_comm

theorem Covariant.average_lift {L : Matrix κ κ ℝ} {D : Matrix ι ι ℝ}
    {B : ι → Matrix κ κ ℝ} (h : Covariant L D B) (A : Matrix ι ι ℝ) :
    average (rotationCommutant L) (lift B A) = lift B (average (rotationCommutant D) A) := by
  apply rotation_average_natural
  · exact fun A => (h.commutator_lift A).symm
  · exact fun A => (h.transpose.commutator_lift A).symm

theorem annihilation_covariant {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) :
    Covariant (secondQuantization L) L annihilation where
  lower i := commutator_annihilation L i
  raise i := by rw [secondQuantization_transpose]; exact commutator_annihilation L.transpose i

end LaughlinGap.RealOccupation

end

end OAI
