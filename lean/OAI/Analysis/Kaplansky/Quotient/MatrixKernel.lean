import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Quotient.NullIdeal

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped Matrix CStarAlgebra ComplexOrder
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace SpectralKernel
variable (d : CuntzDimensionState A)

def single {n : ℕ} (i j : Fin n) (a : A) : Mat A n :=
  CStarMatrix.ofMatrix fun k l => if k=i ∧ l=j then a else 0

def oneByOne (a : A) : Mat A 1 := CStarMatrix.toOneByOne (Fin 1) ℂ A a

@[simp] lemma oneByOne_apply (a : A) (i j : Fin 1) : oneByOne a i j = a := rfl

@[simp] lemma single_apply {n : ℕ} (i j k l : Fin n) (a : A) :
    single i j a k l = if k=i ∧ l=j then a else 0 := rfl

lemma single_star {n : ℕ} (i j : Fin n) (a : A) :
    star (single i j a) = single j i (star a) := by
  ext k l
  simp only [CStarMatrix.star_apply,single_apply]
  split_ifs <;> simp_all [and_comm]

lemma single_mul {n : ℕ} (i j k : Fin n) (a b : A) :
    single i j a * single j k b = single i k (a*b) := by
  ext l t
  simp only [CStarMatrix.mul_apply,single_apply]
  by_cases hi : l=i <;> by_cases hk : t=k <;> simp [hi,hk]

lemma single_compress {n : ℕ} (i j : Fin n) (x : Mat A n) :
    single i i 1*x*single j j 1 = single i j (x i j) := by
  ext k l
  simp only [CStarMatrix.mul_apply,single_apply]
  by_cases hi : k=i <;> by_cases hj : l=j <;> simp [hi,hj]

lemma null_single_iff {n : ℕ} (i j : Fin n) (a : A) :
    IsNull d (single i j a) ↔ IsNull d (oneByOne a) := by
  let r : Matrix (Fin n) (Fin 1) A := fun k _ => if k=i then a else 0
  have hr : CStarMatrix.ofMatrix (r*r.conjTranspose) =
      single i j a*star (single i j a) := by
    rw [single_star,single_mul]
    ext k l
    simp only [CStarMatrix.ofMatrix_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_one,single_apply]
    dsimp [r]
    by_cases hk : k=i <;> by_cases hl : l=i <;> simp [hk,hl]
  have hr' : CStarMatrix.ofMatrix (r.conjTranspose*r) =
      star (oneByOne a)*oneByOne a := by
    ext k l
    simp only [CStarMatrix.ofMatrix_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      CStarMatrix.mul_apply,CStarMatrix.star_apply,oneByOne_apply,Fin.sum_univ_one]
    dsimp [r]
    simp
  have h := gram_swap d r
  rw [hr,hr',val_square_swap] at h
  exact (congrArg (·=0) h).to_iff

lemma null_iff_entries {n : ℕ} (x : Mat A n) :
    IsNull d x ↔ ∀ i j, IsNull d (oneByOne (x i j)) := by
  constructor
  · intro hx i j
    apply (null_single_iff d i j _).1
    rw [← single_compress]
    exact null_mul_right d (null_mul_left d hx _) _
  · intro hx
    have hs (f : Fin n → Fin n → A) (k l : Fin n) :
        (∑ i, ∑ j, if k=i ∧ l=j then f i j else 0) = f k l := by simp [ite_and]
    have he : x = ∑ i, ∑ j, single i j (x i j) := by
      ext k l
      simp only [mat_sum_apply,single_apply]
      exact (hs (fun i j => x i j) k l).symm
    rw [he]
    apply (nullIdeal d n).submodule.sum_mem
    intro i hi
    apply (nullIdeal d n).submodule.sum_mem
    intro j hj
    exact (null_single_iff d i j _).2 (hx i j)

end SpectralKernel
end KaplanskyConsequences

end

end OAI
