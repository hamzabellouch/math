import Mathlib
import OAI.MathematicalPhysics.BFSS.Core
import OAI.MathematicalPhysics.BFSS.MassiveCoercivity

namespace OAI

/-! Orthonormal color coordinates and the literal matrix potential. -/

namespace BFSSQuantum
noncomputable section
open Matrix Finset
open scoped ComplexConjugate
namespace AlgebraData
variable {N : ℕ} (M : AlgebraData N)

def colorCombination (a : ColorIndex N → ℝ) : ColorMatrix N :=
  ∑ A, (a A : ℂ) • M.color A

def matrixCoordinate (x : Boson N) (i : SpaceIndex) : ColorMatrix N :=
  ∑ A : ColorIndex N, (x (i, A) : ℂ) • M.color A

lemma colorCombination_hermitian (a : ColorIndex N → ℝ) :
    (M.colorCombination a).IsHermitian := by
  unfold colorCombination Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro A hA
  simp [Matrix.conjTranspose_smul, (M.color_hermitian A).eq]

lemma colorCombination_traceless (a : ColorIndex N → ℝ) :
    Matrix.trace (M.colorCombination a) = 0 := by
  simp [colorCombination, Matrix.trace_sum, Matrix.trace_smul, M.color_traceless]

lemma colorCombination_pairing (a b : ColorIndex N → ℝ) :
    Matrix.trace (M.colorCombination a * M.colorCombination b) =
      ((∑ A, a A * b A : ℝ) : ℂ) := by
  simp only [colorCombination, Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc,
    mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, M.color_orthonormal]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, mul_comm]

lemma colorCombination_normSq (a : ColorIndex N → ℝ) :
    BFSS.hsNormSq (M.colorCombination a) = ∑ A, (a A)^2 := by
  apply Complex.ofReal_injective
  rw [BFSS.hsNormSq_trace, (M.colorCombination_hermitian a).eq,
    M.colorCombination_pairing]
  simp only [pow_two]

lemma colorCombination_coeff (a : ColorIndex N → ℝ) (A : ColorIndex N) :
    (Matrix.trace (M.color A * M.colorCombination a)).re = a A := by
  simp only [colorCombination, Matrix.mul_sum, mul_smul_comm, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, M.color_orthonormal, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Complex.ofReal_re]

lemma colorCombination_reconstruct (X : ColorMatrix N) (hx : X.IsHermitian)
    (ht : Matrix.trace X = 0) :
    M.colorCombination (fun A => (Matrix.trace (M.color A * X)).re) = X := by
  obtain ⟨a, ha⟩ := M.color_spanning X hx ht
  change X = M.colorCombination a at ha
  rw [ha]
  simp only [M.colorCombination_coeff]

lemma bracket_hermitian (X Y : ColorMatrix N) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (AlgebraData.bracket X Y).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp only [bracket, Matrix.conjTranspose_smul, star_neg, Complex.star_def, Complex.conj_I,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hX.eq, hY.eq, neg_neg]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

lemma bracket_traceless (X Y : ColorMatrix N) :
    Matrix.trace (AlgebraData.bracket X Y) = 0 := by
  rw [bracket, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, smul_zero]

lemma bracket_sum_left {ι : Type*} (s : Finset ι) (X : ι → ColorMatrix N) (Y : ColorMatrix N) :
    AlgebraData.bracket (∑ i ∈ s, X i) Y = ∑ i ∈ s, AlgebraData.bracket (X i) Y := by
  simp only [bracket, Matrix.sum_mul, Matrix.mul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]

lemma bracket_sum_right {ι : Type*} (s : Finset ι) (X : ColorMatrix N) (Y : ι → ColorMatrix N) :
    AlgebraData.bracket X (∑ i ∈ s, Y i) = ∑ i ∈ s, AlgebraData.bracket X (Y i) := by
  simp only [bracket, Matrix.sum_mul, Matrix.mul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]

lemma bracket_smul (a b : ℂ) (X Y : ColorMatrix N) :
    AlgebraData.bracket (a • X) (b • Y) = (a*b) • AlgebraData.bracket X Y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

lemma bracket_colorCombination (a b : ColorIndex N → ℝ) :
    AlgebraData.bracket (M.colorCombination a) (M.colorCombination b) =
      M.colorCombination (fun A => ∑ B, ∑ C, M.structureConstant A B C * a B * b C) := by
  have hb : AlgebraData.bracket (M.colorCombination a) (M.colorCombination b) =
      ∑ B, ∑ C, ((a B : ℂ)*(b C : ℂ)) • AlgebraData.bracket (M.color B) (M.color C) := by
    rw [colorCombination, bracket_sum_left]
    apply Finset.sum_congr rfl
    intro B hB
    rw [colorCombination, bracket_sum_right]
    simp only [bracket_smul]
  rw [← M.colorCombination_reconstruct (AlgebraData.bracket _ _)
    (bracket_hermitian _ _ (M.colorCombination_hermitian a) (M.colorCombination_hermitian b))
    (bracket_traceless _ _)]
  congr 1
  funext A
  simp only [hb, Matrix.mul_sum, mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro C hC
  simp only [structureConstant, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

end AlgebraData
end
end BFSSQuantum

namespace BFSSQuantum
noncomputable section
open Matrix Finset
namespace AlgebraData
variable {N : ℕ} (M : AlgebraData N)

lemma colorCombination_sub (a b : ColorIndex N → ℝ) :
    M.colorCombination (fun A => a A - b A) = M.colorCombination a - M.colorCombination b := by
  simp only [colorCombination, Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]

lemma colorCombination_smul (r : ℝ) (a : ColorIndex N → ℝ) :
    M.colorCombination (fun A => r * a A) = (r : ℂ) • M.colorCombination a := by
  simp only [colorCombination, Complex.ofReal_mul, mul_smul, Finset.smul_sum]

lemma colorCombination_neg (a : ColorIndex N → ℝ) :
    M.colorCombination (fun A => -a A) = -M.colorCombination a := by
  simp only [colorCombination, Complex.ofReal_neg, neg_smul, Finset.sum_neg_distrib]

def matrixConfiguration (x : Boson N) : BFSS.Configuration N :=
  fun i => ⟨M.colorCombination (fun A => x (i,A)), M.colorCombination_hermitian _,
    M.colorCombination_traceless _⟩

lemma matrixConfiguration_norm (x : Boson N) :
    BFSS.configurationNormSq (M.matrixConfiguration x) = ‖x‖^2 := by
  simp only [BFSS.configurationNormSq, matrixConfiguration, M.colorCombination_normSq,
    EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]

def coordinateBracketAll (x : Boson N) (i j : SpaceIndex) (A : ColorIndex N) : ℝ :=
  ∑ B, ∑ C, M.structureConstant A B C * x (i,B) * x (j,C)

lemma coordinate_bracket_matrix (x : Boson N) (i j : SpaceIndex) :
    M.colorCombination (M.coordinateBracketAll x i j) =
      BFSS.realBracket (M.matrixConfiguration x i).val (M.matrixConfiguration x j).val := by
  exact (M.bracket_colorCombination (fun A => x (i,A)) (fun A => x (j,A))).symm

lemma coordinate_bracket_norm (x : Boson N) (i j : SpaceIndex) :
    BFSS.hsNormSq (BFSS.realBracket (M.matrixConfiguration x i).val (M.matrixConfiguration x j).val) =
      ∑ A, (M.coordinateBracketAll x i j A)^2 := by
  rw [← M.coordinate_bracket_matrix, M.colorCombination_normSq]

lemma coordinate_shifted_norm (h m : ℝ) (x : Boson N) (i j k : SpaceIndex) :
    BFSS.hsNormSq ((h : ℂ) • BFSS.realBracket (M.matrixConfiguration x i).val
      (M.matrixConfiguration x j).val - (2*m : ℝ) • (M.matrixConfiguration x k).val) =
      ∑ A, (h*M.coordinateBracketAll x i j A - 2*m*x (k,A))^2 := by
  rw [← M.colorCombination_normSq, M.colorCombination_sub, M.colorCombination_smul,
    M.colorCombination_smul, M.coordinate_bracket_matrix]
  congr 2

lemma coordinateBracketAll_skew (x : Boson N) (i j : SpaceIndex) (A : ColorIndex N) :
    M.coordinateBracketAll x j i A = -M.coordinateBracketAll x i j A := by
  have hm : M.colorCombination (M.coordinateBracketAll x j i) =
      M.colorCombination (fun A => -M.coordinateBracketAll x i j A) := by
    rw [M.colorCombination_neg, M.coordinate_bracket_matrix, M.coordinate_bracket_matrix]
    simp only [BFSS.realBracket, neg_smul, smul_sub]
    abel
  have hc := congrArg (fun X => (Matrix.trace (M.color A * X)).re) hm
  simpa only [M.colorCombination_coeff] using hc

end AlgebraData
end
end BFSSQuantum

end OAI
