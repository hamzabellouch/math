import Mathlib
import OAI.Analysis.Commutator.CornerAlgebra
import OAI.Analysis.Commutator.MatrixCornerHilbert

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

def restrict : A →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun a := (σ a).restrict (hinv a)
  map_one' := by ext x; change σ 1 (x:H)=x; simp
  map_mul' a b := by ext x; change σ (a*b) (x:H)=σ a (σ b x); rw [map_mul]; rfl
  map_add' a b := by ext x; change σ (a+b) (x:H)=σ a x+σ b x; rw [map_add]; rfl
  map_zero' := by ext x; change σ 0 (x:H)=0; simp
  commutes' c := by
    ext x
    change σ (algebraMap ℂ A c) (x:H)=c • (x:H)
    simp only [Algebra.algebraMap_eq_smul_one,map_smul,map_one,smul_apply,one_apply_eq_self]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y:H) (σ (star a) (x:H)) = inner ℂ y (((σ a).restrict (hinv a)).adjoint x)
    rw [adjoint_inner_right]
    change inner ℂ (y:H) (σ (star a) (x:H))=inner ℂ (σ a (y:H)) (x:H)
    rw [map_star,star_eq_adjoint,adjoint_inner_right]

@[simp] lemma restrict_apply (a : A) (x : K) :
    (restrict σ K hinv a x:H)=σ a x := rfl

variable {p : A} (hp : IsStarProjection p)

def corner : Corner hp →⋆ₐ[ℂ] (MatrixCornerHilbert.fixedSpace (σ p) →L[ℂ]
    MatrixCornerHilbert.fixedSpace (σ p)) where
  toFun a := (σ (a:A)).restrict (by
    intro x hx
    rw [MatrixCornerHilbert.mem_fixedSpace] at hx ⊢
    change (σ p*σ (a:A)) x=σ (a:A) x
    rw [←map_mul,a.property.1])
  map_one' := by
    ext x
    exact MatrixCornerHilbert.fixed_apply (σ p) x
  map_mul' a b := by ext x; change σ ((a:A)*(b:A)) (x:H)=σ (a:A) (σ (b:A) x); rw [map_mul]; rfl
  map_add' a b := by ext x; change σ ((a:A)+(b:A)) (x:H)=σ (a:A) x+σ (b:A) x; rw [map_add]; rfl
  map_zero' := by ext x; change σ 0 (x:H)=0; simp
  commutes' c := by
    ext x
    change σ (c • p) (x:H)=c • (x:H)
    rw [map_smul,smul_apply,MatrixCornerHilbert.fixed_apply]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    rw [star_eq_adjoint,adjoint_inner_right]
    change inner ℂ (y:H) (σ (star (a:A)) (x:H))=inner ℂ (σ (a:A) (y:H)) (x:H)
    rw [map_star,star_eq_adjoint,adjoint_inner_right]

@[simp] lemma corner_apply (a : Corner hp) (x : MatrixCornerHilbert.fixedSpace (σ p)) :
    (corner σ hp a x:H)=σ (a:A) x := rfl

end Kadison.ReducingRepresentation

end

end
end

end OAI
