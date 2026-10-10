import OAI.CategoryTheory.Globular.CylinderInterpretation

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsFullCylinder : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)
variable (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))

noncomputable def cylinderRealization : C.Obj ⥤ CutoffModels C q where
  obj S := (cylinderFrame hC q n).shapeRealization.obj S.shape
  map f := ((cylinderInterpretation hC q n hnq H).map f).cylinder
  map_id S := congrArg RepresentedHom.cylinder ((cylinderInterpretation hC q n hnq H).map_id S.shape)
  map_comp f g := congrArg RepresentedHom.cylinder ((cylinderInterpretation hC q n hnq H).map_comp f g)

@[simp] theorem cylinderRealization_base {S T : Shape} (f : S ⟶ T) :
    (cylinderRealization hC q n hnq H).map (C.base f) =
      (cylinderFrame hC q n).shapeRealization.map f :=
  congrArg RepresentedHom.cylinder ((cylinderInterpretation hC q n hnq H).map_base f)

theorem cylinderInterpretation_original {S T : Shape} (f : C.Hom S T) :
    ((cylinderInterpretation hC q n hnq H).map f).original = f :=
  congrArg (fun z : Morphism C C => z.map f) (cylinderInterpretation_projection hC q n hnq H)

noncomputable def fullCylinder (Y : CutoffModels C q) : C.Model where
  presheaf := (cylinderRealization hC q n hnq H).op ⋙ yoneda.obj Y
  sums S b h hl hr := by
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, TheoryData.arity, cylinderRealization_base]
    exact (((cylinderFrame hC q n).shapeRealization_sums S b h hl hr).op.map (yoneda.obj Y)).flip

noncomputable def fullCylinderEndpoint (Y : CutoffModels C q) (ε : Bool) :
    fullCylinder hC q n hnq H Y ⟶ Y.obj where
  app S := ↾(fun a => yonedaEquiv ((cutoffAdjunction hC q).homEquiv _ Y
    ((cylinderShapeEndpoint hC q n ε).app S.unop.shape ≫ a)))
  naturality S T f := by
    apply ConcreteCategory.hom_ext
    intro a
    symm
    change Y.obj.presheaf.map f (yonedaEquiv ((cutoffAdjunction hC q).homEquiv _ Y
      ((cylinderShapeEndpoint hC q n ε).app S.unop.shape ≫ a))) =
      yonedaEquiv ((cutoffAdjunction hC q).homEquiv _ Y
        ((cylinderShapeEndpoint hC q n ε).app T.unop.shape ≫
          (cylinderRealization hC q n hnq H).map f.unop ≫ a))
    have he : (cylinderShapeEndpoint hC q n ε).app T.unop.shape ≫
        (cylinderRealization hC q n hnq H).map f.unop =
        (cutoffRepresentables hC q).map f.unop ≫
          (cylinderShapeEndpoint hC q n ε).app S.unop.shape := by
      let E := (cylinderInterpretation hC q n hnq H).map f.unop
      have ho : (show T.unop ⟶ S.unop from E.original) = f.unop :=
        cylinderInterpretation_original hC q n hnq H f.unop
      cases ε
      · exact E.endpoint₀.trans (congrArg (fun z : T.unop ⟶ S.unop =>
          (cutoffRepresentables hC q).map z ≫ (cylinderShapeEndpoint hC q n false).app S.unop.shape) ho)
      · exact E.endpoint₁.trans (congrArg (fun z : T.unop ⟶ S.unop =>
          (cutoffRepresentables hC q).map z ≫ (cylinderShapeEndpoint hC q n true).app S.unop.shape) ho)
    have ha : (cylinderShapeEndpoint hC q n ε).app T.unop.shape ≫
        (cylinderRealization hC q n hnq H).map f.unop ≫ a =
        (cutoffRepresentables hC q).map f.unop ≫
          ((cylinderShapeEndpoint hC q n ε).app S.unop.shape ≫ a) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ a) he).trans (Category.assoc _ _ _))
    have hadj := (cutoffAdjunction hC q).homEquiv_naturality_left
      (show freeShape C T.unop.shape ⟶ freeShape C S.unop.shape from yoneda.map f.unop)
      ((cylinderShapeEndpoint hC q n ε).app S.unop.shape ≫ a)
    exact (yonedaEquiv_naturality _ f.unop).trans
      ((congrArg yonedaEquiv hadj.symm).trans
        (congrArg (fun z => yonedaEquiv ((cutoffAdjunction hC q).homEquiv _ Y z)) ha.symm))

noncomputable def fullCylinderEvaluation (Y : CutoffModels C q) :
    GlobularSet.Hom (fullCylinder hC q n hnq H Y).underlying ((cylinderFrame hC q n).homGlob Y) where
  app j a := ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫ a
  source_app j a := by
    change ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫
      (cylinderRealization hC q n hnq H).map (C.base (Shape.source j)) ≫ a =
      (cylinderFrame hC q n).diagram.source j ≫ ((cylinderFrame hC q n).shapeGlobeIso (j+1)).inv ≫ a
    erw [cylinderRealization_base, ← Category.assoc,
      ← GlobularFrame.shapeGlobeIso_source_inv, Category.assoc]
  target_app j a := by
    change ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫
      (cylinderRealization hC q n hnq H).map (C.base (Shape.target j)) ≫ a =
      (cylinderFrame hC q n).diagram.target j ≫ ((cylinderFrame hC q n).shapeGlobeIso (j+1)).inv ≫ a
    erw [cylinderRealization_base, ← Category.assoc,
      ← GlobularFrame.shapeGlobeIso_target_inv, Category.assoc]

noncomputable def fullCylinderCoevaluation (Y : CutoffModels C q) :
    GlobularSet.Hom ((cylinderFrame hC q n).homGlob Y) (fullCylinder hC q n hnq H Y).underlying where
  app j a := ((cylinderFrame hC q n).shapeGlobeIso j).hom ≫ a
  source_app j a := by
    change ((cylinderFrame hC q n).shapeGlobeIso j).hom ≫
      (cylinderFrame hC q n).diagram.source j ≫ a =
      (cylinderRealization hC q n hnq H).map (C.base (Shape.source j)) ≫
        ((cylinderFrame hC q n).shapeGlobeIso (j+1)).hom ≫ a
    erw [cylinderRealization_base]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a)
      ((cylinderFrame hC q n).shapeGlobeIso_source j).symm).trans (Category.assoc _ _ _))
  target_app j a := by
    change ((cylinderFrame hC q n).shapeGlobeIso j).hom ≫
      (cylinderFrame hC q n).diagram.target j ≫ a =
      (cylinderRealization hC q n hnq H).map (C.base (Shape.target j)) ≫
        ((cylinderFrame hC q n).shapeGlobeIso (j+1)).hom ≫ a
    erw [cylinderRealization_base]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a)
      ((cylinderFrame hC q n).shapeGlobeIso_target j).symm).trans (Category.assoc _ _ _))

@[simp] theorem fullCylinderEvaluation_coevaluation (Y : CutoffModels C q) :
    (fullCylinderEvaluation hC q n hnq H Y).comp (fullCylinderCoevaluation hC q n hnq H Y) =
      GlobularSet.Hom.id _ := by
  ext j a
  exact Iso.hom_inv_id_assoc _ _

@[simp] theorem fullCylinderCoevaluation_evaluation (Y : CutoffModels C q) :
    (fullCylinderCoevaluation hC q n hnq H Y).comp (fullCylinderEvaluation hC q n hnq H Y) =
      GlobularSet.Hom.id _ := by
  ext j a
  exact Iso.inv_hom_id_assoc _ _

@[simp] theorem fullCylinderEndpoint_evaluation (Y : CutoffModels C q) (ε : Bool) :
    underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε) =
      ((fullCylinderEvaluation hC q n hnq H Y).comp
        ((cylinderEndpoint hC q n ε).pre Y)).comp (cutoffDiskEvaluation hC q Y) := by
  ext j a
  change cutoffCellEquiv hC q Y j ((cylinderShapeEndpoint hC q n ε).app (Shape.globe j) ≫ a) =
    cutoffCellEquiv hC q Y j ((cylinderEndpoint hC q n ε).obj j ≫
      ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫ a)
  erw [← Category.assoc, cylinderShapeEndpoint_globe_inv]
end GlobularTheory.Model
end Grothendieck

end OAI
