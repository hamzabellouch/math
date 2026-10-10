import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.NerveProduct

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentStable
open FreeChains ComponentTranslation ConnectedProduct

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {X Y X' Y':SSet}
noncomputable def pullD (f:X⟶nerve C) (g:Y⟶nerve C) (q:ℕ) :
    (X⊗Y).homology Z q ⟶ object (C:=C) q := SSet.homologyMap (f⊗ₘg) Z q ≫ binaryD q
omit [SymmetricCategory C] in
@[reassoc] lemma pullD_comp (f:X⟶X') (g:Y⟶Y') (F:X'⟶nerve C) (G:Y'⟶nerve C) (q:ℕ) :
    SSet.homologyMap (f⊗ₘg) Z q ≫ pullD F G q=pullD (f≫F) (g≫G) q := by
  rw [pullD,←SSet.homologyMap_comp_assoc,tensorHom_comp_tensorHom, pullD]
omit [SymmetricCategory C] in
lemma pullD_congr {D E:Type} [Category.{0} D] [Category.{0} E]
    {f f':D⥤C} {g g':E⥤C} (α:f≅f') (β:g≅g') (q:ℕ) :
    pullD (nerveMap f) (nerveMap g) q=pullD (nerveMap f') (nerveMap g') q := by
  rw [pullD,pullD,NerveProduct.homology_congr α β]
omit [SymmetricCategory C] in
lemma pullD_left (f:X⟶nerve C) (g:Y⟶nerve C) (U:C) (q:ℕ) :
    pullD (f≫nerveMap (tensorLeft U)) g q=pullD f g q := by
  conv_lhs => rw [←Category.comp_id g]
  rw [pullD,←tensorHom_comp_tensorHom,SSet.homologyMap_comp,Category.assoc,binaryD_left]
  rfl
lemma pullD_right (f:X⟶nerve C) (g:Y⟶nerve C) (U:C) (q:ℕ) :
    pullD f (g≫nerveMap (tensorLeft U)) q=pullD f g q := by
  conv_lhs => rw [←Category.comp_id f]
  rw [pullD,←tensorHom_comp_tensorHom,SSet.homologyMap_comp,Category.assoc,binaryD_second_left]
  rfl
lemma pairLeft_tensor (f:X⟶X') (g:Y⟶Y') (y:Y.obj (op ⦋0⦌)) :
    pairLeft X Y y ≫ (f⊗ₘg)=f≫pairLeft X' Y' (g.app _ y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [pairLeft]
  · simp [pairLeft,SSet.const_comp]
lemma pairRight_tensor (f:X⟶X') (g:Y⟶Y') (x:X.obj (op ⦋0⦌)) :
    pairRight X Y x ≫ (f⊗ₘg)=g≫pairRight X' Y' (f.app _ x) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [pairRight,SSet.const_comp]
  · simp [pairRight]
@[reassoc] lemma inclusion_pullD (f:X⟶nerve C) (g:Y⟶nerve C)
    (x:X.obj (op ⦋0⦌)) (y:Y.obj (op ⦋0⦌)) (q:ℕ) (hq:q≠0) :
    ConnectedProduct.inclusion X Y x y q ≫ pullD f g q=0 := by
  apply biprod.hom_ext'
  · simp only [ConnectedProduct.inclusion,biprod.inl_desc_assoc,pullD]
    rw [←SSet.homologyMap_comp_assoc,pairLeft_tensor,SSet.homologyMap_comp_assoc,pairLeft_binaryD _ q hq,comp_zero]
    simp
  · simp only [ConnectedProduct.inclusion,biprod.inr_desc_assoc,pullD]
    rw [←SSet.homologyMap_comp_assoc,pairRight_tensor,SSet.homologyMap_comp_assoc,pairRight_binaryD _ q hq,comp_zero]
    simp
lemma pullD_kernel_value (f:X⟶nerve C) (g:Y⟶nerve C)
    (x:X.obj (op ⦋0⦌)) (y:Y.obj (op ⦋0⦌)) (q:ℕ) (hq:q≠0)
    (z:((X⊗Y).homology Z q:A)) :
    ∃w:((X⊗Y).homology Z q:A), projection X Y q w=0 ∧ pullD f g q w=pullD f g q z := by
  let inc:=ConnectedProduct.inclusion X Y x y q
  refine ⟨z-inc (projection X Y q z),?_,?_⟩
  · rw [map_sub]
    have h:=congrArg (fun k=>k (projection X Y q z)) (inclusion_projection X Y x y q hq)
    change projection X Y q (inc (projection X Y q z))=projection X Y q z at h
    rw [h,sub_self]
  · rw [map_sub]
    have h:=congrArg (fun k=>k (projection X Y q z)) (inclusion_pullD f g x y q hq)
    change pullD f g q (inc (projection X Y q z))=0 at h
    rw [h,sub_zero]
end ComponentStable

end

end OAI
