import Mathlib

namespace OAI

noncomputable section

namespace KKProjectionSupport

noncomputable section

open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A]

def matrixUnitLinear (e : ι → ι → A) : Matrix ι ι ℂ →ₗ[ℂ] A where
  toFun x := ∑ i, ∑ j, x i j • e i j
  map_add' x y := by simp only [Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp only [Matrix.smul_apply,smul_smul,Finset.smul_sum]; rfl

omit [DecidableEq ι] in
@[simp] theorem matrixUnitLinear_apply (e : ι → ι → A) (x : Matrix ι ι ℂ) :
    matrixUnitLinear e x=∑ i, ∑ j, x i j • e i j := rfl

theorem matrixUnitLinear_mul (e : ι → ι → A)
    (hm : ∀ i j k l, e i j * e k l = if j=k then e i l else 0)
    (x y : Matrix ι ι ℂ) : matrixUnitLinear e (x*y)=matrixUnitLinear e x*matrixUnitLinear e y := by
  symm
  calc
    matrixUnitLinear e x*matrixUnitLinear e y =
        ∑ i, ∑ j, ∑ k, ∑ l, (x i j*y k l) • (e i j*e k l) := by
      simp only [matrixUnitLinear_apply]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm]
    _ = ∑ i, ∑ j, ∑ l, (x i j*y j l) • e i l := by
      simp only [hm,smul_ite,smul_zero,Finset.sum_ite_irrel,Finset.sum_const_zero]
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    _ = matrixUnitLinear e (x*y) := by
      simp only [matrixUnitLinear_apply,Matrix.mul_apply,Finset.sum_smul,mul_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]

theorem matrixUnitLinear_one (e : ι → ι → A) (h1 : ∑ i, e i i=1) :
    matrixUnitLinear e 1=1 := by
  simpa only [matrixUnitLinear_apply,Matrix.one_apply,ite_smul,one_smul,zero_smul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true] using h1

variable [StarRing A] [StarModule ℂ A]

omit [DecidableEq ι] in
theorem matrixUnitLinear_star (e : ι → ι → A) (hs : ∀ i j, star (e i j)=e j i)
    (x : Matrix ι ι ℂ) : matrixUnitLinear e (star x)=star (matrixUnitLinear e x) := by
  simp only [matrixUnitLinear_apply,star_sum,star_smul,hs,Matrix.star_apply]
  rw [Finset.sum_comm]

def matrixUnitHom (e : ι → ι → A)
    (hm : ∀ i j k l, e i j*e k l=if j=k then e i l else 0)
    (h1 : ∑ i, e i i=1) (hs : ∀ i j, star (e i j)=e j i) :
    Matrix ι ι ℂ →⋆ₐ[ℂ] A where
  toFun := matrixUnitLinear e
  map_zero' := (matrixUnitLinear e).map_zero
  map_one' := matrixUnitLinear_one e h1
  map_add' := (matrixUnitLinear e).map_add
  map_mul' := matrixUnitLinear_mul e hm
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,matrixUnitLinear_one e h1,
      Algebra.algebraMap_eq_smul_one]
  map_star' := matrixUnitLinear_star e hs

@[simp] theorem matrixUnitHom_apply (e : ι → ι → A)
    (hm : ∀ i j k l, e i j*e k l=if j=k then e i l else 0)
    (h1 : ∑ i, e i i=1) (hs : ∀ i j, star (e i j)=e j i) (x : Matrix ι ι ℂ) :
    matrixUnitHom e hm h1 hs x=∑ i, ∑ j, x i j • e i j := rfl

end

end KKProjectionSupport
end

end OAI
