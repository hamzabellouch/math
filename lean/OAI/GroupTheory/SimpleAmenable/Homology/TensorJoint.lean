import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FreeChains

namespace OAI

section

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace ChainTensor
open FreeChains

variable (S T:ShortComplex (ChainComplex A ℕ)) (s:S.Splitting) (t:T.Splitting)
lemma splitting_tensor_identity :
    (s.r⊗ₘt.r) ≫ (S.f⊗ₘT.f) +
      (𝟙 S.X₂⊗ₘT.g) ≫ ((s.r≫S.f)⊗ₘt.s) +
      (S.g⊗ₘ𝟙 T.X₂) ≫ (s.s⊗ₘ𝟙 T.X₂) = 𝟙 (S.X₂⊗T.X₂) := by
  have tensor_add {sourceLeft targetLeft sourceRight targetRight : ChainComplex A ℕ}
      (left : sourceLeft ⟶ targetLeft) (right₁ right₂ : sourceRight ⟶ targetRight) :
      left ⊗ₘ (right₁ + right₂) = left ⊗ₘ right₁ + left ⊗ₘ right₂ := by
    apply HomologicalComplex.Hom.ext
    funext degree
    apply mapBifunctor.hom_ext
    intro leftDegree rightDegree totalDegree
    change ιMapBifunctor sourceLeft sourceRight (curriedTensor A) c leftDegree rightDegree degree totalDegree ≫
        (mapBifunctorMap left (right₁ + right₂) (curriedTensor A) c).f degree =
      ιMapBifunctor sourceLeft sourceRight (curriedTensor A) c leftDegree rightDegree degree totalDegree ≫
        ((mapBifunctorMap left right₁ (curriedTensor A) c).f degree +
          (mapBifunctorMap left right₂ (curriedTensor A) c).f degree)
    simp [Preadditive.comp_add]
  have add_tensor {sourceLeft targetLeft sourceRight targetRight : ChainComplex A ℕ}
      (left₁ left₂ : sourceLeft ⟶ targetLeft) (right : sourceRight ⟶ targetRight) :
      (left₁ + left₂) ⊗ₘ right = left₁ ⊗ₘ right + left₂ ⊗ₘ right := by
    apply HomologicalComplex.Hom.ext
    funext degree
    apply mapBifunctor.hom_ext
    intro leftDegree rightDegree totalDegree
    change ιMapBifunctor sourceLeft sourceRight (curriedTensor A) c leftDegree rightDegree degree totalDegree ≫
        (mapBifunctorMap (left₁ + left₂) right (curriedTensor A) c).f degree =
      ιMapBifunctor sourceLeft sourceRight (curriedTensor A) c leftDegree rightDegree degree totalDegree ≫
        ((mapBifunctorMap left₁ right (curriedTensor A) c).f degree +
          (mapBifunctorMap left₂ right (curriedTensor A) c).f degree)
    simp [Preadditive.comp_add]
  simp only [tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←tensor_add,t.id,←add_tensor,s.id,id_tensorHom_id]
include s t in
lemma homology_joint_kernel (n:ℕ) (hz:IsZero ((S.X₁⊗T.X₁).homology n))
    (x:(S.X₂⊗T.X₂).homology n)
    (h1:homologyMap (𝟙 S.X₂⊗ₘT.g) n x=0)
    (h2:homologyMap (S.g⊗ₘ𝟙 T.X₂) n x=0) : x=0 := by
  have hm : homologyMap ((s.r⊗ₘt.r) ≫ (S.f⊗ₘT.f)) n=0 := by
    rw [homologyMap_comp,hz.eq_of_src (homologyMap (S.f⊗ₘT.f) n) 0,comp_zero]
  have hid := congrArg (fun f => homologyMap f n) (splitting_tensor_identity S T s t)
  simp only [homologyMap_add] at hid
  rw [hm,homologyMap_comp,homologyMap_comp,homologyMap_id] at hid
  have hh := congrArg (fun f => f x) hid
  change 0 + homologyMap ((s.r≫S.f)⊗ₘt.s) n (homologyMap (𝟙 S.X₂⊗ₘT.g) n x) +
    homologyMap (s.s⊗ₘ𝟙 T.X₂) n (homologyMap (S.g⊗ₘ𝟙 T.X₂) n x) = x at hh
  simpa only [h1,h2,map_zero,add_zero] using hh.symm
end ChainTensor

end

end

end OAI
