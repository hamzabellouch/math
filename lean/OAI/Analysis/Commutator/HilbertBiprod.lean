import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

abbrev Space (H G : Type*) := WithLp 2 (H × G)

def inlL : H →L[ℂ] Space H G :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H G).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ H).prod 0)

def inrL : G →L[ℂ] Space H G :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H G).symm.toContinuousLinearMap.comp
    ((0 : G →L[ℂ] H).prod (ContinuousLinearMap.id ℂ G))

@[simp] lemma inlL_apply (x : H) : inlL (G:=G) x=WithLp.toLp 2 (x,0) := rfl

@[simp] lemma inrL_apply (y : G) : inrL (H:=H) y=WithLp.toLp 2 (0,y) := rfl

def inl : H →ₗᵢ[ℂ] Space H G :=
  (inlL (H:=H) (G:=G)).toLinearMap.isometryOfInner (by
    intro x y
    simp [WithLp.prod_inner_apply])

def inr : G →ₗᵢ[ℂ] Space H G :=
  (inrL (H:=H) (G:=G)).toLinearMap.isometryOfInner (by
    intro x y
    simp [WithLp.prod_inner_apply])

@[simp] lemma inl_apply (x : H) : inl (G:=G) x=WithLp.toLp 2 (x,0) := rfl

@[simp] lemma inr_apply (y : G) : inr (H:=H) y=WithLp.toLp 2 (0,y) := rfl

def block (S : H →L[ℂ] H) (T : G →L[ℂ] G) : Space H G →L[ℂ] Space H G :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H G).symm.toContinuousLinearMap.comp
    ((S.prodMap T).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H G).toContinuousLinearMap)

@[simp] lemma block_apply (S : H →L[ℂ] H) (T : G →L[ℂ] G) (x : Space H G) :
    block S T x=WithLp.toLp 2 (S x.ofLp.1,T x.ofLp.2) := rfl

lemma ext {S T : Space H G →L[ℂ] Space H G}
    (h : ∀ x,(S x).ofLp=(T x).ofLp) : S=T := by
  ext x
  exact WithLp.ofLp_injective 2 (h x)

@[simp] lemma block_zero : block (0:H →L[ℂ] H) (0:G →L[ℂ] G)=0 := by
  apply ext
  intro x
  rfl

@[simp] lemma block_one : block (1:H →L[ℂ] H) (1:G →L[ℂ] G)=1 := by
  apply ext
  intro x
  rfl

lemma block_mul (S S' : H →L[ℂ] H) (T T' : G →L[ℂ] G) :
    block (S*S') (T*T')=block S T*block S' T' := by
  apply ext
  intro x
  rfl

lemma block_add (S S' : H →L[ℂ] H) (T T' : G →L[ℂ] G) :
    block (S+S') (T+T')=block S T+block S' T' := by
  apply ext
  intro x
  rfl

lemma block_smul (z : ℂ) (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block (z • S) (z • T)=z • block S T := by
  apply ext
  intro x
  rfl

variable [CompleteSpace H] [CompleteSpace G]

lemma block_star (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block (star S) (star T)=star (block S T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left,
    block_apply,WithLp.prod_inner_apply]

variable {A : Type*} [CStarAlgebra A]

def diagHom (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G)) :
    A →⋆ₐ[ℂ] (Space H G →L[ℂ] Space H G) where
  toFun a := block (φ a) (ψ a)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul,block_mul]
  map_zero' := by simp
  map_add' a b := by simp only [map_add,block_add]
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, block_smul, block_one]
  map_star' a := by simp only [map_star,block_star]

@[simp] lemma diagHom_apply (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (a : A) : diagHom φ ψ a=block (φ a) (ψ a) := rfl

omit [CompleteSpace H] [CompleteSpace G] in
lemma block_inl (S : H →L[ℂ] H) (T : G →L[ℂ] G) (x : H) :
    block S T (inl x)=inl (S x) := by simp

omit [CompleteSpace H] [CompleteSpace G] in
lemma block_inr (S : H →L[ℂ] H) (T : G →L[ℂ] G) (y : G) :
    block S T (inr y)=inr (T y) := by simp

lemma diagHom_injective (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (hφ : Function.Injective φ) : Function.Injective (diagHom φ ψ) := by
  intro a b hab
  apply hφ
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun U : Space H G →L[ℂ] Space H G => (U (inl x)).ofLp.1) hab
  simpa using h

end Kadison.HilbertBiprod

end

end
end

end OAI
