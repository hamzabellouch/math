import OAI.CategoryTheory.Globular.CylinderExtension

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]

@[reassoc] theorem shapeGlobeIso_source (B : GlobularFrame K) (j : ℕ) :
    B.shapeRealization.map (Shape.source j) ≫ (B.shapeGlobeIso (j+1)).hom =
      (B.shapeGlobeIso j).hom ≫ B.diagram.source j := by
  simpa only [Shape.source, CoGlobularObject.face_succ, CoGlobularObject.adjacent, Bool.false_eq_true, ↓reduceIte]
    using B.shapeGlobeIso_face (Nat.lt_succ_self j) false

@[reassoc] theorem shapeGlobeIso_target (B : GlobularFrame K) (j : ℕ) :
    B.shapeRealization.map (Shape.target j) ≫ (B.shapeGlobeIso (j+1)).hom =
      (B.shapeGlobeIso j).hom ≫ B.diagram.target j := by
  simpa only [Shape.target, CoGlobularObject.face_succ, CoGlobularObject.adjacent, ↓reduceIte]
    using B.shapeGlobeIso_face (Nat.lt_succ_self j) true

@[reassoc] theorem shapeGlobeIso_source_inv (B : GlobularFrame K) (j : ℕ) :
    B.diagram.source j ≫ (B.shapeGlobeIso (j+1)).inv =
      (B.shapeGlobeIso j).inv ≫ B.shapeRealization.map (Shape.source j) := by
  apply (cancel_mono (B.shapeGlobeIso (j+1)).hom).1
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    shapeGlobeIso_source, Iso.inv_hom_id_assoc]

@[reassoc] theorem shapeGlobeIso_target_inv (B : GlobularFrame K) (j : ℕ) :
    B.diagram.target j ≫ (B.shapeGlobeIso (j+1)).inv =
      (B.shapeGlobeIso j).inv ≫ B.shapeRealization.map (Shape.target j) := by
  apply (cancel_mono (B.shapeGlobeIso (j+1)).hom).1
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    shapeGlobeIso_target, Iso.inv_hom_id_assoc]

end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsOperations : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

@[reassoc] theorem cylinderShapeEndpoint_globe_inv (ε : Bool) (j : ℕ) :
    (cylinderEndpoint hC q n ε).obj j ≫ ((cylinderFrame hC q n).shapeGlobeIso j).inv =
      (cylinderShapeEndpoint hC q n ε).app (Shape.globe j) := by
  apply (cancel_mono ((cylinderFrame hC q n).shapeGlobeIso j).hom).1
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (cylinderShapeEndpoint_globe hC q n ε j).symm

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] in
@[simp] theorem cutoffRepresentables_source (j : ℕ) :
    (cutoffRepresentables hC q).map (C.base (Shape.source j)) =
      (cutoffDiskFrame hC q).diagram.source j := by
  rw [cutoffDiskFrame_source]
  rfl

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] in
@[simp] theorem cutoffRepresentables_target (j : ℕ) :
    (cutoffRepresentables hC q).map (C.base (Shape.target j)) =
      (cutoffDiskFrame hC q).diagram.target j := by
  rw [cutoffDiskFrame_target]
  rfl

end GlobularTheory.Model
end Grothendieck

end OAI
