import OAI.Combinatorics.PolynomialVacuum.Algebra.TensorYangBaxter

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem Pzero_transpose : Pzero.transpose=Pzero := by
  ext a b; simp only [Pzero,Matrix.transpose_apply]; ring

theorem Pone_transpose : Pone.transpose=Pone := by
  ext a b; simp only [Pone,Matrix.transpose_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro h _; ring

theorem Ptwo_transpose : Ptwo.transpose=Ptwo := by
  simp [Ptwo,Matrix.transpose_sub,Pone_transpose,Pzero_transpose]

theorem numerator_transpose (x y : ℂ) : (exchangeNumerator x y).transpose=exchangeNumerator x y := by
  simp [exchangeNumerator,Matrix.transpose_add,Matrix.transpose_smul,
    Pzero_transpose,Pone_transpose,Ptwo_transpose]

theorem matrix12_transpose (A : Matrix Pair Pair ℂ) : (matrix12 A).transpose=matrix12 A.transpose := by
  ext ⟨a,b,c⟩ ⟨d,e,f⟩
  simp [matrix12,Matrix.transpose_apply,eq_comm]

theorem matrix23_transpose (A : Matrix Pair Pair ℂ) : (matrix23 A).transpose=matrix23 A.transpose := by
  ext ⟨a,b,c⟩ ⟨d,e,f⟩
  simp [matrix23,Matrix.transpose_apply,eq_comm]

theorem matrix_yang_baxter_reverse (x y z : ℂ) :
    matrix12 (exchangeNumerator y z) * matrix23 (exchangeNumerator x z) *
      matrix12 (exchangeNumerator x y) =
    matrix23 (exchangeNumerator x y) * matrix12 (exchangeNumerator x z) *
      matrix23 (exchangeNumerator y z) := by
  have h := congrArg Matrix.transpose (matrix_yang_baxter x y z)
  simpa only [Matrix.transpose_mul,matrix12_transpose,matrix23_transpose,
    numerator_transpose,Matrix.mul_assoc] using h

theorem tensor_yang_baxter_reverse {I : Type*} [DecidableEq I] {i j k : I}
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) (x y z : ℂ) (W : SpinTensor I ℂ) :
    pairAction i j (exchangeNumerator y z)
      (pairAction j k (exchangeNumerator x z) (pairAction i j (exchangeNumerator x y) W)) =
    pairAction j k (exchangeNumerator x y)
      (pairAction i j (exchangeNumerator x z) (pairAction j k (exchangeNumerator y z) W)) := by
  rw [← tripleAction_matrix12 hik hjk, ← tripleAction_matrix23 i j k,
    ← tripleAction_matrix12 hik hjk, ← tripleAction_matrix23 i j k,
    ← tripleAction_matrix12 hik hjk, ← tripleAction_matrix23 i j k]
  simp only [tripleAction_mul hij hik hjk,← Matrix.mul_assoc,matrix_yang_baxter_reverse]

noncomputable def pairLinear {I : Type*} [DecidableEq I] (i j : I) (A : Matrix Pair Pair ℂ) :
    Module.End ℂ (SpinTensor I ℂ) where
  toFun := pairAction i j A
  map_add' W V := by
    funext s
    simp [pairAction,mul_add,Finset.sum_add_distrib]
  map_smul' c W := by
    funext s
    simp only [pairAction,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro ab _; ring

noncomputable def siteR (i : ℕ) (x y : ℂ) : Module.End ℂ (SpinTensor ℕ ℂ) :=
  pairLinear i (i+1) (exchangeNumerator x y)

theorem siteR_far_comm {i j : ℕ} (h : i + 1 < j ∨ j + 1 < i) (x y u v : ℂ) :
    siteR i x y*siteR j u v=siteR j u v*siteR i x y := by
  ext W s
  exact congrFun (pairAction_comm (by omega : i≠j) (by omega : i≠j+1)
    (by omega : i+1≠j) (by omega : i+1≠j+1) _ _ W) s

theorem siteR_yang_baxter (i : ℕ) (x y z : ℂ) :
    siteR i y z*siteR (i+1) x z*siteR i x y =
      siteR (i+1) x y*siteR i x z*siteR (i+1) y z := by
  ext W s
  exact congrFun (tensor_yang_baxter_reverse (by omega : i≠i+1) (by omega : i≠i+1+1)
    (by omega : i+1≠i+1+1) x y z W) s

end PolynomialVacuumAlgebra

end OAI
