import OAI.Analysis.Triangular.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.MatrixBounds
def colNorm {m n : Type*} [Fintype m] (A : Matrix m n ℝ) (j : n) : ℝ := ∑ i, |A i j|
def matNorm {m n : Type*} [Fintype m] [Fintype n] [Nonempty n] (A : Matrix m n ℝ) : ℝ :=
  Finset.univ.sup' (by classical exact Finset.univ_nonempty) (colNorm A)

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

omit [Fintype n] in
lemma colNorm_nonneg (A : Matrix m n ℝ) (j : n) : 0 ≤ colNorm A j :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)
lemma colNorm_le_matNorm [Nonempty n] (A : Matrix m n ℝ) (j : n) :
    colNorm A j ≤ matNorm A := by
  classical
  exact Finset.le_sup' (f := colNorm A) (Finset.mem_univ j)
lemma matNorm_nonneg [Nonempty n] (A : Matrix m n ℝ) : 0 ≤ matNorm A := by
  obtain ⟨j⟩ := ‹Nonempty n›
  exact (colNorm_nonneg A j).trans (colNorm_le_matNorm A j)
lemma matNorm_le [Nonempty n] {A : Matrix m n ℝ} {c : ℝ}
    (h : ∀ j, colNorm A j ≤ c) : matNorm A ≤ c := by
  classical
  exact (Finset.sup'_le_iff _ _).mpr (fun j _ => h j)
omit [Fintype n] in
lemma colNorm_add (A B : Matrix m n ℝ) (j : n) :
    colNorm (A+B) j ≤ colNorm A j + colNorm B j := by
  unfold colNorm
  simp only [Matrix.add_apply,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_add_le _ _)
lemma matNorm_add [Nonempty n] (A B : Matrix m n ℝ) :
    matNorm (A+B) ≤ matNorm A + matNorm B := by
  apply matNorm_le
  intro j
  exact (colNorm_add A B j).trans (add_le_add (colNorm_le_matNorm A j) (colNorm_le_matNorm B j))
omit [Fintype n] in
lemma colNorm_neg (A : Matrix m n ℝ) (j : n) : colNorm (-A) j = colNorm A j := by
  simp only [colNorm,Matrix.neg_apply,abs_neg]
lemma matNorm_neg [Nonempty n] (A : Matrix m n ℝ) : matNorm (-A) = matNorm A := by
  simp only [matNorm,colNorm_neg]
lemma matNorm_sub [Nonempty n] (A B : Matrix m n ℝ) :
    matNorm (A-B) ≤ matNorm A + matNorm B := by
  simpa only [sub_eq_add_neg,matNorm_neg] using matNorm_add A (-B)
omit [Fintype p] in
lemma colNorm_mul [Nonempty n] (A : Matrix m n ℝ) (B : Matrix n p ℝ) (j : p) :
    colNorm (A*B) j ≤ matNorm A * colNorm B j := by
  classical
  calc
    colNorm (A*B) j ≤ ∑ i, ∑ k, |A i k * B k j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ k, colNorm A k * |B k j| := by
      rw [Finset.sum_comm]
      simp only [abs_mul,Finset.sum_mul,colNorm]
    _ ≤ ∑ k, matNorm A * |B k j| := Finset.sum_le_sum
      (fun k _ => mul_le_mul_of_nonneg_right (colNorm_le_matNorm A k) (abs_nonneg _))
    _ = matNorm A * colNorm B j := by simp only [colNorm,Finset.mul_sum]
lemma matNorm_mul [Nonempty n] [Nonempty p] (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    matNorm (A*B) ≤ matNorm A * matNorm B := by
  apply matNorm_le
  intro j
  exact (colNorm_mul A B j).trans (mul_le_mul_of_nonneg_left
    (colNorm_le_matNorm B j) (matNorm_nonneg A))
lemma matNorm_one [DecidableEq n] [Nonempty n] : matNorm (1 : Matrix n n ℝ) = 1 := by
  classical
  have hh (j : n) : colNorm (1 : Matrix n n ℝ) j = 1 := by
    unfold colNorm
    simp only [Matrix.one_apply,apply_ite abs,abs_one,abs_zero]
    simp
  obtain ⟨j⟩ := ‹Nonempty n›
  apply le_antisymm
  · exact matNorm_le (fun i => (hh i).le)
  · rw [← hh j]
    exact colNorm_le_matNorm _ j
lemma matNorm_pow [DecidableEq n] [Nonempty n] (A : Matrix n n ℝ) (k : ℕ) :
    matNorm (A^k) ≤ (matNorm A)^k := by
  induction k with
  | zero => simp [matNorm_one]
  | succ k ih =>
    rw [pow_succ,pow_succ]
    exact (matNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ih (matNorm_nonneg A))

lemma norm_of_inverse_residual [DecidableEq n] [Nonempty n]
    {A V H C : Matrix n n ℝ} {b e h : ℝ}
    (hv : (1-A)*V = 1-H) (hc : matNorm C ≤ b)
    (he : matNorm (C*(1-A)-1) ≤ e) (hh : matNorm H ≤ h)
    (hb0 : 0 ≤ b) :
    matNorm V ≤ b*(1+h)+e*matNorm V := by
  have heq : V = C-C*H-(C*(1-A)-1)*V := by
    have heq := congrArg (fun X => C*X) hv
    rw [← Matrix.mul_assoc] at heq
    change C*(1-A)*V = C*(1-H) at heq
    rw [Matrix.mul_sub C 1 H,Matrix.mul_one] at heq
    calc
      V = C-C*H-((C*(1-A))*V-V) := by rw [heq]; abel
      _ = _ := by rw [Matrix.sub_mul,Matrix.one_mul]
  calc
    matNorm V ≤ matNorm (C-C*H)+matNorm ((C*(1-A)-1)*V) := by
      conv_lhs => rw [heq]
      exact matNorm_sub _ _
    _ ≤ (matNorm C+matNorm (C*H))+matNorm (C*(1-A)-1)*matNorm V :=
      add_le_add (matNorm_sub _ _) (matNorm_mul _ _)
    _ ≤ (b+b*h)+e*matNorm V := by
      apply add_le_add
      · exact add_le_add hc ((matNorm_mul _ _).trans
          (mul_le_mul hc hh (matNorm_nonneg H) hb0))
      · exact mul_le_mul_of_nonneg_right he (matNorm_nonneg V)
    _ = _ := by ring

lemma inverse_residual_approx [DecidableEq n] [Nonempty n]
    {A V H C : Matrix n n ℝ}
    (hv : (1-A)*V = 1-H) :
    matNorm (V-C) ≤ matNorm C*matNorm H+matNorm (C*(1-A)-1)*matNorm V := by
  have heq : V-C = -(C*H+(C*(1-A)-1)*V) := by
    have heq := congrArg (fun X => C*X) hv
    rw [← Matrix.mul_assoc] at heq
    change C*(1-A)*V = C*(1-H) at heq
    rw [Matrix.mul_sub C 1 H,Matrix.mul_one] at heq
    rw [Matrix.sub_mul,Matrix.one_mul]
    rw [heq]
    abel
  rw [heq,matNorm_neg]
  exact (matNorm_add _ _).trans (add_le_add (matNorm_mul _ _) (matNorm_mul _ _))

end AtomicTriangular.MatrixBounds

namespace AtomicTriangular.MatrixBounds
open Matrix
variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
def vecNorm (v : n → ℝ) : ℝ := ∑ i, |v i|
omit [Nonempty n] [DecidableEq n] in
lemma vecNorm_nonneg (v : n → ℝ) : 0 ≤ vecNorm v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
omit [Nonempty n] [DecidableEq n] in
lemma vecNorm_zero_iff (v : n → ℝ) : vecNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext i
    have hi : |v i| ≤ vecNorm v := (Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    rw [h] at hi
    exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
  · rintro rfl; simp [vecNorm]
omit [DecidableEq n] in
lemma matrix_vecNorm (A : Matrix n n ℝ) (v : n → ℝ) :
    vecNorm (A.mulVec v) ≤ matNorm A * vecNorm v := by
  calc
    _ ≤ ∑ i, ∑ j, |A i j * v j| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ j, colNorm A j * |v j| := by
      rw [Finset.sum_comm]
      simp only [abs_mul,Finset.sum_mul,colNorm]
    _ ≤ ∑ j, matNorm A * |v j| := Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_right (colNorm_le_matNorm A j) (abs_nonneg _))
    _ = _ := by simp only [vecNorm,Finset.mul_sum]
lemma isUnit_of_residual (A C : Matrix n n ℝ) (he : matNorm (C*A-1) < 1) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hh
  have hzero : A.mulVec (v-w) = 0 := by rw [mulVec_sub,hh,sub_self]
  have hres : (C*A-1).mulVec (v-w) = -(v-w) := by
    rw [Matrix.sub_mulVec,← Matrix.mulVec_mulVec, hzero,Matrix.mulVec_zero,Matrix.one_mulVec,zero_sub]
  have hb := matrix_vecNorm (C*A-1) (v-w)
  rw [hres] at hb
  have hneg : vecNorm (-(v-w)) = vecNorm (v-w) := by simp only [vecNorm, Pi.neg_apply, abs_neg]
  rw [hneg] at hb
  have hz := vecNorm_nonneg (v-w)
  have hv : vecNorm (v-w) = 0 := by nlinarith
  exact sub_eq_zero.mp ((vecNorm_zero_iff _).mp hv)
lemma inverse_bound_of_residual (A C : Matrix n n ℝ) (b e : ℝ)
    (hc : matNorm C ≤ b) (he : matNorm (C*A-1) ≤ e) (_hb : 0 ≤ b) (he1 : e < 1) :
    matNorm A⁻¹ ≤ b/(1-e) := by
  have hu : IsUnit A := isUnit_of_residual A C (he.trans_lt he1)
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hid : A⁻¹ = C-(C*A-1)*A⁻¹ := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv A hd,Matrix.mul_one]
    abel
  have hx : matNorm A⁻¹ ≤ b+e*matNorm A⁻¹ := by
    calc
      _ ≤ matNorm C + matNorm ((C*A-1)*A⁻¹) := by
        conv_lhs => rw [hid]
        exact matNorm_sub _ _
      _ ≤ b+e*matNorm A⁻¹ := add_le_add hc ((matNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right he (matNorm_nonneg _)))
  apply (le_div_iff₀ (sub_pos.mpr he1)).mpr
  nlinarith
lemma inverse_error_of_residual (A C : Matrix n n ℝ) (b e : ℝ)
    (hc : matNorm C ≤ b) (he : matNorm (C*A-1) ≤ e) (hb : 0 ≤ b) (he0 : 0 ≤ e) (he1 : e < 1) :
    matNorm (A⁻¹-C) ≤ e*b/(1-e) := by
  have hu : IsUnit A := isUnit_of_residual A C (he.trans_lt he1)
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hid : A⁻¹-C = -((C*A-1)*A⁻¹) := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv A hd,Matrix.mul_one]
    abel
  rw [hid,matNorm_neg]
  exact (matNorm_mul _ _).trans ((mul_le_mul he
    (inverse_bound_of_residual A C b e hc he hb he1) (matNorm_nonneg _) he0).trans_eq (by ring))
end AtomicTriangular.MatrixBounds
end

end OAI
