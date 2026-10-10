import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Quotient.MatrixKernel
import OAI.Analysis.Kaplansky.Quotient.FiniteQuotient

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped Matrix CStarAlgebra ComplexOrder
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def matrixMap (f : A →⋆ₐ[ℂ] B) (n : ℕ) : Mat A n →⋆ₐ[ℂ] Mat B n where
  toFun x := x.map f
  map_zero' := by ext; simp [CStarMatrix.zero_apply]
  map_one' := by
    ext i j
    by_cases h : i=j <;> simp [CStarMatrix.one_apply,h]
  map_add' x y := by ext; simp [CStarMatrix.add_apply,map_add]
  map_mul' x y := by ext; simp [CStarMatrix.mul_apply,map_sum,map_mul]
  commutes' r := by
    ext i j
    by_cases h : i=j
    · simp only [CStarMatrix.map_apply,CStarMatrix.algebraMap_apply,ite_eq_left h]
      exact AlgHomClass.commutes f r
    · simp [CStarMatrix.algebraMap_apply,h]
  map_star' x := by ext; simp [CStarMatrix.star_apply,map_star]

@[simp] lemma matrixMap_apply (f : A →⋆ₐ[ℂ] B) (n : ℕ) (x : Mat A n) (i j : Fin n) :
    matrixMap f n x i j = f (x i j) := rfl

lemma matrixMap_surjective (f : A →⋆ₐ[ℂ] B) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (matrixMap f n) := by
  intro x
  refine ⟨CStarMatrix.ofMatrix (fun i j => (hf (x i j)).choose), ?_⟩
  ext i j
  exact (hf (x i j)).choose_spec

namespace SpectralKernel
variable (d : CuntzDimensionState A)
abbrev FaithfulQuotient := (nullIdeal d 1).Quotient

def quotientHom : A →⋆ₐ[ℂ] FaithfulQuotient d :=
  (nullIdeal d 1).mkStarAlgHom.comp (CStarMatrix.toOneByOne (Fin 1) ℂ A).toStarAlgHom

lemma quotientHom_surjective : Function.Surjective (quotientHom d) :=
  (nullIdeal d 1).mk_surjective.comp (CStarMatrix.toOneByOne (Fin 1) ℂ A).surjective

lemma quotientHom_eq_zero (a : A) : quotientHom d a = 0 ↔ IsNull d (oneByOne a) :=
  (nullIdeal d 1).mk_eq_zero (oneByOne a)

variable [Nontrivial A]

instance faithfulQuotient_nontrivial : Nontrivial (FaithfulQuotient d) := by
  apply nontrivial_of_ne (1 : FaithfulQuotient d) 0
  intro h
  have hzero : (nullIdeal d 1).quotientMap 1 = 0 := by simpa only [map_one] using h
  have hn : IsNull d (1 : Mat A 1) := ((nullIdeal d 1).mk_eq_zero _).1 hzero
  have ht := val_zero_of_null d zero_le_one hn
  simp at ht

lemma matrixMap_quotient_eq_zero {n : ℕ} (x : Mat A n) :
    matrixMap (quotientHom d) n x = 0 ↔ IsNull d x := by
  rw [null_iff_entries]
  constructor
  · intro h i j
    apply (quotientHom_eq_zero d _).1
    have he := congrArg (fun M : Mat (FaithfulQuotient d) n => M i j) h
    simpa only [matrixMap_apply,CStarMatrix.zero_apply] using he
  · intro h
    ext i j
    exact (quotientHom_eq_zero d _).2 (h i j)

theorem faithfulQuotient_stablyFinite : StablyFinite (FaithfulQuotient d) := by
  intro n hn v hv
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨x,hx⟩ := matrixMap_surjective (quotientHom d) (quotientHom_surjective d) n v
  have hzero : matrixMap (quotientHom d) n (star x*x-1) = 0 := by
    simp only [map_sub,map_mul,map_star,map_one,hx,hv,sub_self]
  have hnull := (matrixMap_quotient_eq_zero d _).1 hzero
  have hnull' := finite_mod_null d x hnull
  have hzero' := (matrixMap_quotient_eq_zero d _).2 hnull'
  simpa only [map_sub,map_mul,map_star,map_one,hx,sub_eq_zero] using hzero'

end SpectralKernel
end KaplanskyConsequences

end

end OAI
