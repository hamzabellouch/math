import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def inverseMatrixPair (A : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ :=
  ∑ j, ∑ i, A⁻¹ i j*x j*y i

lemma inverseMatrixPair_eq_dot (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A x y = y ⬝ᵥ A⁻¹.mulVec x := by
  simp only [inverseMatrixPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma inverseMatrixPair_self_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef) (x : ι → ℝ) :
    0 ≤ inverseMatrixPair A x x := by
  rw [inverseMatrixPair_eq_dot]
  simpa using hA.inv.posSemidef.dotProduct_mulVec_nonneg x

lemma inverseMatrixPair_symm {A : Matrix ι ι ℝ} (hA : A.IsSymm) (x y : ι → ℝ) :
    inverseMatrixPair A x y = inverseMatrixPair A y x := by
  have hi : A⁻¹.IsSymm := by rw [Matrix.IsSymm,Matrix.transpose_nonsing_inv,hA.eq]
  unfold inverseMatrixPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.transpose_apply A⁻¹ i j,hi.eq]
  ring

lemma inverseMatrixPair_add_left (A : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    inverseMatrixPair A (fun i => x i+y i) z = inverseMatrixPair A x z+inverseMatrixPair A y z := by
  simp only [inverseMatrixPair,mul_add,add_mul,Finset.sum_add_distrib]

lemma inverseMatrixPair_add_right (A : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    inverseMatrixPair A x (fun i => y i+z i) = inverseMatrixPair A x y+inverseMatrixPair A x z := by
  simp only [inverseMatrixPair,mul_add,Finset.sum_add_distrib]

lemma inverseMatrixPair_smul_left (A : Matrix ι ι ℝ) (t : ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A (fun i => t*x i) y = t*inverseMatrixPair A x y := by
  simp only [inverseMatrixPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma inverseMatrixPair_smul_right (A : Matrix ι ι ℝ) (t : ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A x (fun i => t*y i) = t*inverseMatrixPair A x y := by
  simp only [inverseMatrixPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/- Cauchy--Schwarz for a positive definite inverse matrix, including zero vectors. -/
lemma inverseMatrixPair_cauchy {A : Matrix ι ι ℝ} (hA : A.PosDef) (x y : ι → ℝ) :
    inverseMatrixPair A x y^2 ≤ inverseMatrixPair A x x*inverseMatrixPair A y y := by
  have hs : A.IsSymm := by simpa only [Matrix.isHermitian_iff_isSymm] using hA.isHermitian
  have hq (t : ℝ) : 0 ≤ inverseMatrixPair A y y*(t*t)+
      (2*inverseMatrixPair A x y)*t+inverseMatrixPair A x x := by
    have hh := inverseMatrixPair_self_nonneg hA (fun i => x i+t*y i)
    rw [inverseMatrixPair_add_left,inverseMatrixPair_add_right,inverseMatrixPair_add_right,
      inverseMatrixPair_smul_right,inverseMatrixPair_smul_left,inverseMatrixPair_smul_left,
      inverseMatrixPair_smul_right,inverseMatrixPair_symm hs y x] at hh
    nlinarith [hh]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

end AffineBernstein
end

end OAI
