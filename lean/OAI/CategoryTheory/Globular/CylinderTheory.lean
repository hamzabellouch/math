import OAI.CategoryTheory.Globular.ShapeFrame

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]
theorem shapeRealization_sums (B : GlobularFrame K) (S : Shape) (b h : ℕ)
    (hl : b < S.1) (hr : b < h) :
    IsPushout (B.shapeRealization.map (S.seam hl))
      (B.shapeRealization.map (Shape.face hr false))
      (B.shapeRealization.map (S.inl b h hl hr))
      (B.shapeRealization.map (S.inr b h hl hr)) :=
  (Shape.liftedRealization_pushout S b h hl hr).map B.realization
end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsTheory : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

noncomputable def shapeFrameNatIso :
    C.toTheoryData.arity ⋙ cutoffRepresentables hC q ≅ (cutoffDiskFrame hC q).shapeRealization :=
  NatIso.ofComponents (shapeFrameIso hC q) (fun f => shapeFrameIso_naturality hC q f)

noncomputable def cylinderShapeEndpoint (ε : Bool) :
    C.toTheoryData.arity ⋙ cutoffRepresentables hC q ⟶ (cylinderFrame hC q n).shapeRealization :=
  (shapeFrameNatIso hC q).hom ≫ (cylinderEndpoint hC q n ε).shapeEndpoint

@[reassoc] theorem cylinderShapeEndpoint_globe (ε : Bool) (j : ℕ) :
    (cylinderShapeEndpoint hC q n ε).app (Shape.globe j) ≫
      ((cylinderFrame hC q n).shapeGlobeIso j).hom = (cylinderEndpoint hC q n ε).obj j := by
  change ((shapeFrameIso hC q (Shape.globe j)).hom ≫
    (cylinderEndpoint hC q n ε).shapeEndpoint.app _) ≫ _ = _
  erw [shapeFrameIso_globe, Category.assoc]
  exact GlobularFrame.shapeEndpoint_globe _ _

theorem cutoffRepresentables_sums (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout ((cutoffRepresentables hC q).map (C.base (S.seam hl)))
      ((cutoffRepresentables hC q).map (C.base (Shape.face hr false)))
      ((cutoffRepresentables hC q).map (C.base (S.inl b h hl hr)))
      ((cutoffRepresentables hC q).map (C.base (S.inr b h hl hr))) := by
  exact ((cutoffDiskFrame hC q).shapeRealization_sums S b h hl hr).of_iso'
    (shapeFrameIso hC q (Shape.globe b)) (shapeFrameIso hC q S)
    (shapeFrameIso hC q (Shape.globe h)) (shapeFrameIso hC q (S.attach b h hl hr))
    (shapeFrameIso_naturality hC q _).symm (shapeFrameIso_naturality hC q _).symm
    (shapeFrameIso_naturality hC q _).symm (shapeFrameIso_naturality hC q _).symm

noncomputable abbrev cylinderTheory : GlobularTheory.{v} :=
  representedTheory (cutoffRepresentables hC q) (cylinderFrame hC q n).shapeRealization
    (cylinderShapeEndpoint hC q n false) (cylinderShapeEndpoint hC q n true)
    (cylinderFrame hC q n).shapeRealization_sums (cutoffRepresentables_sums hC q)
noncomputable abbrev cylinderProjection : Morphism (cylinderTheory hC q n) C :=
  representedProjection (cutoffRepresentables hC q) (cylinderFrame hC q n).shapeRealization
    (cylinderShapeEndpoint hC q n false) (cylinderShapeEndpoint hC q n true)
    (cylinderFrame hC q n).shapeRealization_sums (cutoffRepresentables_sums hC q)

end GlobularTheory.Model
end Grothendieck

end OAI
