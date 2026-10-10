import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

namespace ArExplicit

universe u

variable {k A B C D : Type u} [Semiring k]
variable [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
variable [AddCommMonoid C] [Module k C] [AddCommMonoid D] [Module k D]

def linearRetractEquiv (i : A →ₗ[k] B) (p : B →ₗ[k] A) (hpi : p.comp i = LinearMap.id)
    (j : C →ₗ[k] D) (q : D →ₗ[k] C) (hqj : q.comp j = LinearMap.id)
    (e : B ≃ₗ[k] D) (he : ∀ b, e (i (p b)) = j (q (e b))) : A ≃ₗ[k] C where
  toFun a := q (e (i a))
  invFun c := p (e.symm (j c))
  left_inv a := by
    change p (e.symm (j (q (e (i a))))) = a
    rw [← he, e.symm_apply_apply]
    exact (DFunLike.congr_fun hpi _).trans (DFunLike.congr_fun hpi a)
  right_inv c := by
    change q (e (i (p (e.symm (j c))))) = c
    rw [he, e.apply_symm_apply]
    exact (DFunLike.congr_fun hqj _).trans (DFunLike.congr_fun hqj c)
  map_add' a b := by simp
  map_smul' r a := by simp

end ArExplicit

end OAI
