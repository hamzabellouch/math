import OAI.Algebra.Finitistic.Selected.SelectedFixedDiagram
import OAI.Algebra.Finitistic.Localization.SourceOddDoubleEvaluation
import OAI.Algebra.Finitistic.Localization.DiagramEvaluationSquares

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedDiagramEvaluation
open QuadraticEncoding SelectedFixedDiagram SourceImageEvaluation
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

abbrev F := SourceImageEvaluation.evaluation (Y := Y) encoding
abbrev G := completed (Y := Y) encoding
abbrev target := imageDerived (k := ℂ) (Y := Y) e ⊞ (imageDerived (k := ℂ) (Y := Y) e)⟦(3 : ℤ)⟧
def targetAction (r : SelectionRing) : target (Y := Y) ⟶ target (Y := Y) :=
  biprod.map (imageCorner (k := ℂ) (Y := Y) e (alpha r)) ((imageCorner (k := ℂ) (Y := Y) e (alpha r))⟦(3 : ℤ)⟧')

/-- Evaluation of the one fixed actual V0 is precisely eY direct-sum eY[3]. -/
def V0Iso : (F (Y := Y)).obj fixed.V0 ≅ target (Y := Y) :=
  (factors (Y := Y) encoding).symm.app fixed.V0 ≪≫
    ((G (Y := Y)).mapIso fixed.iso ≪≫ oddDoubleImageIso (Y := Y) encoding e idem)

/-- The V0 identification intertwines every selected algebra element on both summands. -/
theorem V0_action (r : SelectionRing) :
    (F (Y := Y)).map (fixed.rho r) ≫ (V0Iso (Y := Y)).hom =
      (V0Iso (Y := Y)).hom ≫ targetAction (Y := Y) r := by
  have hf := (factors (Y := Y) encoding).inv.naturality (fixed.rho r)
  have hi := congrArg (fun f => (G (Y := Y)).map f) (fixed.equivariant r)
  simp only [Functor.map_comp] at hi
  have ho := oddDouble_selecting_square (Y := Y) encoding e idem central alpha r
  exact DiagramEvaluationSquares.compose _ _ _
    ((factors (Y := Y) encoding).symm.app fixed.V0)
    ((factors (Y := Y) encoding).symm.app fixed.V0)
    ((G (Y := Y)).mapIso fixed.iso ≪≫ oddDoubleImageIso (Y := Y) encoding e idem)
    ((G (Y := Y)).mapIso fixed.iso ≪≫ oddDoubleImageIso (Y := Y) encoding e idem)
    hf (DiagramEvaluationSquares.compose _ _ _
      ((G (Y := Y)).mapIso fixed.iso) ((G (Y := Y)).mapIso fixed.iso)
      (oddDoubleImageIso (Y := Y) encoding e idem) (oddDoubleImageIso (Y := Y) encoding e idem)
      hi ho)

abbrev sourceEvaluation := SourceEvaluation.finite
  (SourceActionEvaluation.representation (Y := Y) encoding) ⋙ (FiniteProjectiveHomotopy.derivedEmbedding ℂ).toEssImage

def sourceFactors : SourceVerdier.q P ⋙ F (Y := Y) ≅ sourceEvaluation (Y := Y) :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
    (SourceEvaluation.finiteFactors (SourceActionEvaluation.representation (Y := Y) encoding))
    (FiniteProjectiveHomotopy.derivedEmbedding ℂ).toEssImage

def D0Iso : (sourceEvaluation (Y := Y)).obj fixed.D0 ≅ target (Y := Y) :=
  (sourceFactors (Y := Y)).symm.app fixed.D0 ≪≫ ((F (Y := Y)).mapIso fixed.phi0 ≪≫ V0Iso (Y := Y))
def D1Iso : (sourceEvaluation (Y := Y)).obj fixed.D1 ≅ target (Y := Y) :=
  (sourceFactors (Y := Y)).symm.app fixed.D1 ≪≫ ((F (Y := Y)).mapIso fixed.phi1 ≪≫ V0Iso (Y := Y))
def D2Iso : (sourceEvaluation (Y := Y)).obj fixed.D2 ≅ target (Y := Y) :=
  (sourceFactors (Y := Y)).symm.app fixed.D2 ≪≫ ((F (Y := Y)).mapIso fixed.phi2 ≪≫ V0Iso (Y := Y))

/-- Every first-family arrow of the same fixed K diagram has its selected action. -/
theorem D_arrow01 (a : Fin (encoding.generators+1)) :
    (sourceEvaluation (Y := Y)).map (fixed.f a) ≫ (D1Iso (Y := Y)).hom =
      (D0Iso (Y := Y)).hom ≫ targetAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) := by
  have hn := (sourceFactors (Y := Y)).inv.naturality (fixed.f a)
  have hp := congrArg (fun f => (F (Y := Y)).map f) (fixed.arrow01 a)
  simp only [Functor.map_comp] at hp
  exact DiagramEvaluationSquares.compose _ _ _
    ((sourceFactors (Y := Y)).symm.app fixed.D0) ((sourceFactors (Y := Y)).symm.app fixed.D1)
    ((F (Y := Y)).mapIso fixed.phi0 ≪≫ V0Iso (Y := Y))
    ((F (Y := Y)).mapIso fixed.phi1 ≪≫ V0Iso (Y := Y)) hn
    (DiagramEvaluationSquares.compose _ _ _
      ((F (Y := Y)).mapIso fixed.phi0) ((F (Y := Y)).mapIso fixed.phi1)
      (V0Iso (Y := Y)) (V0Iso (Y := Y)) hp (V0_action _))

theorem D_arrow12 (a : Fin (encoding.generators+1)) :
    (sourceEvaluation (Y := Y)).map (fixed.g a) ≫ (D2Iso (Y := Y)).hom =
      (D1Iso (Y := Y)).hom ≫ targetAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) := by
  have hn := (sourceFactors (Y := Y)).inv.naturality (fixed.g a)
  have hp := congrArg (fun f => (F (Y := Y)).map f) (fixed.arrow12 a)
  simp only [Functor.map_comp] at hp
  exact DiagramEvaluationSquares.compose _ _ _
    ((sourceFactors (Y := Y)).symm.app fixed.D1) ((sourceFactors (Y := Y)).symm.app fixed.D2)
    ((F (Y := Y)).mapIso fixed.phi1 ≪≫ V0Iso (Y := Y))
    ((F (Y := Y)).mapIso fixed.phi2 ≪≫ V0Iso (Y := Y)) hn
    (DiagramEvaluationSquares.compose _ _ _
      ((F (Y := Y)).mapIso fixed.phi1) ((F (Y := Y)).mapIso fixed.phi2)
      (V0Iso (Y := Y)) (V0Iso (Y := Y)) hp (V0_action _))

theorem targetAction_one : targetAction (Y := Y) (1 : SelectionRing) = 𝟙 _ := by
  apply (cancel_epi (V0Iso (Y := Y)).hom).mp
  rw [← V0_action,map_one]
  change (F (Y := Y)).map (𝟙 fixed.V0) ≫ _ = _
  rw [CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id]

theorem distinguished_arrow01 :
    (sourceEvaluation (Y := Y)).map (fixed.f 0) ≫ (D1Iso (Y := Y)).hom = (D0Iso (Y := Y)).hom := by
  have h := D_arrow01 (Y := Y) 0
  simpa only [RelationBasisAction.arrow,Fin.cases_zero,targetAction_one,Category.comp_id] using h

theorem distinguished_arrow12 :
    (sourceEvaluation (Y := Y)).map (fixed.g 0) ≫ (D2Iso (Y := Y)).hom = (D1Iso (Y := Y)).hom := by
  have h := D_arrow12 (Y := Y) 0
  simpa only [RelationBasisAction.arrow,Fin.cases_zero,targetAction_one,Category.comp_id] using h

/-- The same globally chosen K diagram evaluates correctly for every finite module. -/
theorem fixed_diagram_evaluates :
    ∃ (i0 : (sourceEvaluation (Y := Y)).obj fixed.D0 ≅ target (Y := Y))
      (i1 : (sourceEvaluation (Y := Y)).obj fixed.D1 ≅ target (Y := Y))
      (i2 : (sourceEvaluation (Y := Y)).obj fixed.D2 ≅ target (Y := Y)),
      (∀ a, (sourceEvaluation (Y := Y)).map (fixed.f a) ≫ i1.hom =
        i0.hom ≫ targetAction (Y := Y) (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a)) ∧
      (∀ b, (sourceEvaluation (Y := Y)).map (fixed.g b) ≫ i2.hom =
        i1.hom ≫ targetAction (Y := Y) (RelationBasisAction.arrow (SelectionEncoding.generator encoding) b)) :=
  ⟨D0Iso,D1Iso,D2Iso,D_arrow01,D_arrow12⟩

omit [FiniteDimensional ℂ Y] in
/-- Exact vector formula for the selected action, including the alpha restriction. -/
theorem targetAction_on_image (r : SelectionRing) (y : imageSpace (k := ℂ) (Y := Y) e) :
    ((imageCornerEnd (action (k := ℂ) (Y := Y) e).hom (action (k := ℂ) (Y := Y) (alpha r)).hom) y).val =
      (action (k := ℂ) (Y := Y) (alpha r)).hom y.val :=
  imageCorner_restriction e (alpha r) idem (central (alpha r)) y
end LittleFinitistic.SelectedDiagramEvaluation

end

end OAI
