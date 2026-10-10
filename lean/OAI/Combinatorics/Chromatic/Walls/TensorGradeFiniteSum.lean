import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TensorGradeFunctor

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
open scoped TensorProduct
variable {M N X Y D : Type*} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N] [AddCommGroup X] [Module ℚ X]
  [AddCommGroup Y] [Module ℚ Y] [Fintype D]

lemma tensorGradeLift_sum_left (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : D → ∀ u,FGrade F u →ₗ[ℚ] X) (g : ∀ v,FGrade G v →ₗ[ℚ] Y)
    (W : ℤ) (x : TensorGrade F G W) :
    tensorGradeLift F G hF hG (fun u=>∑ d,f d u) g W x=
      ∑ d,tensorGradeLift F G hF hG (f d) g W x := by
  induction x using tensorGrade_induction F G hF hG W with
  | hz => simp only [map_zero,Finset.sum_const_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,Finset.sum_add_distrib]
  | ht u x y => simp only [tensorGradeLift_part,LinearMap.sum_apply,TensorProduct.sum_tmul]

lemma tensorGradeLift_sum_right (F : ℤ → Submodule ℚ M) (G : ℤ → Submodule ℚ N)
    (hF : Antitone F) (hG : Antitone G)
    (f : ∀ u,FGrade F u →ₗ[ℚ] X) (g : D → ∀ v,FGrade G v →ₗ[ℚ] Y)
    (W : ℤ) (x : TensorGrade F G W) :
    tensorGradeLift F G hF hG f (fun v=>∑ d,g d v) W x=
      ∑ d,tensorGradeLift F G hF hG f (g d) W x := by
  induction x using tensorGrade_induction F G hF hG W with
  | hz => simp only [map_zero,Finset.sum_const_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,Finset.sum_add_distrib]
  | ht u x y => simp only [tensorGradeLift_part,LinearMap.sum_apply,TensorProduct.tmul_sum]
end ElementaryPositivity.LinearFiltration

end

end OAI
