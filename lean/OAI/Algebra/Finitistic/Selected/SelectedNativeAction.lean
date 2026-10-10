import OAI.Algebra.Finitistic.Selected.SelectedNativeEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedNativeEvaluation
open QuadraticEncoding SourceImageEvaluation FiniteProjectiveHomotopy SelectedFixedDiagram
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

abbrev imageEnd (r : SelectionRing) := imageCornerEnd
  (action (k := ℂ) (Y := Y) e).hom (action (k := ℂ) (Y := Y) (alpha r)).hom
abbrev moduleIso := (SelectedImageComparison.equiv (Y := Y)).toModuleIso

def HAction (r : SelectionRing) : End (H (Y := Y)) :=
  (moduleIso (Y := Y)).inv ≫ imageEnd (Y := Y) r ≫ (moduleIso (Y := Y)).hom

/-- The conjugated map is the primary selectionStep module action, on every vector. -/
theorem HAction_apply (r : SelectionRing) (x : H (Y := Y)) :
    (HAction (Y := Y) r).hom x = SelectedImageComparison.moduleAction (Y := Y) r x := by
  have h := SelectedImageComparison.equiv_action (Y := Y) r
    ((SelectedImageComparison.equiv (Y := Y)).symm x)
  dsimp only [HAction,moduleIso,LinearEquiv.toModuleIso] at *
  simp only [LinearEquiv.apply_symm_apply] at h
  exact h

lemma module_square (r : SelectionRing) :
    imageEnd (Y := Y) r ≫ (moduleIso (Y := Y)).hom =
      (moduleIso (Y := Y)).hom ≫ HAction (Y := Y) r := by
  simp only [HAction,Iso.hom_inv_id_assoc]

variable [FiniteDimensional ℂ Y]

def HKAction (r : SelectionRing) : End (HK (Y := Y)) :=
  (inclusion ℂ).preimage ((vectorStalk (k := ℂ)).map (HAction (Y := Y) r))
def HDerivedAction (r : SelectionRing) : End (HDerived (Y := Y)) :=
  (derivedEmbedding ℂ).toEssImage.map (HKAction (Y := Y) r)

lemma imageIsoK_hom : (inclusion ℂ).map (imageIsoK (Y := Y)).hom =
    (vectorStalk (k := ℂ)).map (moduleIso (Y := Y)).hom := by
  simp only [imageIsoK,Functor.preimageIso,Functor.mapIso_hom]
  erw [Functor.map_preimage]

lemma image_square (r : SelectionRing) :
    imageCorner (k := ℂ) (Y := Y) e (alpha r) ≫ (imageIso (Y := Y)).hom =
      (imageIso (Y := Y)).hom ≫ HDerivedAction (Y := Y) r := by
  apply (derivedTargetInclusion (k := ℂ)).map_injective
  rw [Functor.map_comp,Functor.map_comp]
  dsimp only [imageCorner]
  erw [Functor.map_preimage]
  change DerivedCategory.Qh.map ((vectorStalk (k := ℂ)).map (imageEnd (Y := Y) r)) ≫
    DerivedCategory.Qh.map ((inclusion ℂ).map (imageIsoK (Y := Y)).hom) =
    DerivedCategory.Qh.map ((inclusion ℂ).map (imageIsoK (Y := Y)).hom) ≫
    DerivedCategory.Qh.map ((inclusion ℂ).map (HKAction (Y := Y) r))
  rw [imageIsoK_hom]
  dsimp only [HKAction]
  erw [Functor.map_preimage]
  erw [← Functor.map_comp,← Functor.map_comp,← Functor.map_comp,← Functor.map_comp,module_square]
  rfl

abbrev targetAction (r : SelectionRing) : End (target (Y := Y)) :=
  biprod.map (HDerivedAction (Y := Y) r) ((HDerivedAction (Y := Y) r)⟦(3 : ℤ)⟧')

lemma target_square (r : SelectionRing) :
    SelectedDiagramEvaluation.targetAction (Y := Y) r ≫ (targetIso (Y := Y)).hom =
      (targetIso (Y := Y)).hom ≫ targetAction (Y := Y) r := by
  have h := image_square (Y := Y) r
  have hs := congrArg (shiftFunctor (FiniteVectorDerived.{0,v} (k := ℂ)) (3 : ℤ)).map h
  simp only [Functor.map_comp] at hs
  dsimp only [SelectedDiagramEvaluation.targetAction,targetIso,targetAction,biprod.mapIso]
  apply biprod.hom_ext
  · simp only [Category.assoc,biprod.map_fst,biprod.map_fst_assoc,h]
  · simp only [Category.assoc,biprod.map_snd,biprod.map_snd_assoc,Functor.mapIso_hom,hs]

/-- The fixed V0 evaluates equivariantly to the primary H(Y) plus H(Y)[3]. -/
theorem V0_action (r : SelectionRing) :
    (SelectedDiagramEvaluation.F (Y := Y)).map (fixed.rho r) ≫ (V0Iso (Y := Y)).hom =
      (V0Iso (Y := Y)).hom ≫ targetAction (Y := Y) r :=
  DiagramEvaluationSquares.compose _ _ _ SelectedDiagramEvaluation.V0Iso
    SelectedDiagramEvaluation.V0Iso targetIso targetIso
    (SelectedDiagramEvaluation.V0_action r) (target_square r)

theorem D_arrow01 (a : Fin (encoding.generators+1)) :
    (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).map (fixed.f a) ≫ (D1Iso (Y := Y)).hom =
      (D0Iso (Y := Y)).hom ≫ targetAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  DiagramEvaluationSquares.compose _ _ _ SelectedDiagramEvaluation.D0Iso
    SelectedDiagramEvaluation.D1Iso targetIso targetIso
    (SelectedDiagramEvaluation.D_arrow01 a) (target_square _)

theorem D_arrow12 (a : Fin (encoding.generators+1)) :
    (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).map (fixed.g a) ≫ (D2Iso (Y := Y)).hom =
      (D1Iso (Y := Y)).hom ≫ targetAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  DiagramEvaluationSquares.compose _ _ _ SelectedDiagramEvaluation.D1Iso
    SelectedDiagramEvaluation.D2Iso targetIso targetIso
    (SelectedDiagramEvaluation.D_arrow12 a) (target_square _)
end LittleFinitistic.SelectedNativeEvaluation

end

end OAI
