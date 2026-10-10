import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def tensorMatrix (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ := fun a b => ∏ i, A (a i) (b i)

theorem tensorMatrix_mul (N : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix N (A*B) = tensorMatrix N A * tensorMatrix N B := by
  ext a c
  simp only [tensorMatrix,Matrix.mul_apply,← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i b => A (a i) b*B b (c i))

theorem tensorMatrix_one (N : ℕ) : tensorMatrix N 1 = 1 := by
  classical
  ext a b
  simp only [tensorMatrix,Matrix.one_apply]
  by_cases h : a=b
  · subst b; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem tensorMatrix_conjTranspose (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix N Aᴴ = (tensorMatrix N A)ᴴ := by
  ext a b
  simp [tensorMatrix,Matrix.conjTranspose_apply]

theorem tensorMatrix_unitary (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    tensorMatrix N A ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose,← tensorMatrix_conjTranspose,← tensorMatrix_mul]
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  rw [Matrix.star_eq_conjTranspose] at h
  rw [h,tensorMatrix_one]

abbrev SourceSU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

noncomputable def sourceTensorRepresentation (Q : ℕ) : SourceSU2 →*
    Matrix (Fin Q → Fin 2) (Fin Q → Fin 2) ℂ where
  toFun g := tensorMatrix Q g.val
  map_one' := tensorMatrix_one Q
  map_mul' g h := tensorMatrix_mul Q g.val h.val

 theorem sourceTensorRepresentation_unitary (Q : ℕ) (g : SourceSU2) :
    sourceTensorRepresentation Q g ∈ Matrix.unitaryGroup (Fin Q → Fin 2) ℂ :=
  tensorMatrix_unitary Q g.val g.property.1

end Laughlin.Rotation

end OAI
