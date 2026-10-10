import OAI.Algebra.Finitistic.Selected.SelectedUnderlyingHomology

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedChainAction
open QuadraticEncoding SelectedFixedDiagram SelectedNativeEvaluation SelectedChainHomology
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

lemma HAction_one : HAction (Y := Y) 1 = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext x
  rw [HAction_apply]
  apply Subtype.ext
  change selectionAutomorphism 1 (1 : SelectionRing) • x.val = x.val
  rw [map_one,one_smul]

/-- In the underlying Y, the selected action is exactly restriction of alpha(r). -/
lemma HAction_val (r : SelectionRing) (x : H (Y := Y)) :
    ((HAction (Y := Y) r).hom x).val = alpha r • x.val := by
  rw [HAction_apply]
  rfl

variable [FiniteDimensional ℂ Y]

lemma distinguished01 (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap
      (SelectedTensorComparison.tensorMap (representation (Y := Y)) (SelectedChainDiagram.fixedChain.f 0)) n ≫
        (SelectedChainHomology.D1Iso n hn).hom = (SelectedChainHomology.D0Iso n hn).hom := by
  simpa only [RelationBasisAction.arrow,Fin.cases_zero,HAction_one,Category.comp_id] using
    (fixed_arrow01 (Y := Y) 0 n hn)
lemma distinguished12 (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap
      (SelectedTensorComparison.tensorMap (representation (Y := Y)) (SelectedChainDiagram.fixedChain.g 0)) n ≫
        (SelectedChainHomology.D2Iso n hn).hom = (SelectedChainHomology.D1Iso n hn).hom := by
  simpa only [RelationBasisAction.arrow,Fin.cases_zero,HAction_one,Category.comp_id] using
    (fixed_arrow12 (Y := Y) 0 n hn)

/-- Every actual first arrow, on every homology class in either selected degree. -/
lemma arrow01_val (a : Fin (encoding.generators+1))
    (f : UnderlyingRepresentatives.complex P fixed.D0 ⟶ UnderlyingRepresentatives.complex P fixed.D1)
    (hf : (HomotopyCategory.quotient _ _).map f = (SourceModelBridge.ambient P).map (fixed.f a))
    (n : ℤ) (hn : n = 0 ∨ n = -3) (x : (complex (Y := Y) fixed.D0).homology n) :
    ((SelectedChainHomology.D1Iso n hn).hom.hom
      ((HomologicalComplex.homologyMap (SelectedUnderlyingHomology.tensorMap (Y := Y) f) n).hom x)).val =
      alpha (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) •
        ((SelectedChainHomology.D0Iso n hn).hom.hom x).val := by
  have h := congrArg (fun q => q.hom x) (SelectedUnderlyingHomology.arrow01 (Y := Y) a f hf n hn)
  change (SelectedChainHomology.D1Iso n hn).hom.hom
      ((HomologicalComplex.homologyMap (SelectedUnderlyingHomology.tensorMap (Y := Y) f) n).hom x) =
    (HAction (Y := Y) (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a)).hom
      ((SelectedChainHomology.D0Iso n hn).hom.hom x) at h
  exact (congrArg Subtype.val h).trans (HAction_val _ _)

lemma arrow12_val (a : Fin (encoding.generators+1))
    (g : UnderlyingRepresentatives.complex P fixed.D1 ⟶ UnderlyingRepresentatives.complex P fixed.D2)
    (hg : (HomotopyCategory.quotient _ _).map g = (SourceModelBridge.ambient P).map (fixed.g a))
    (n : ℤ) (hn : n = 0 ∨ n = -3) (x : (complex (Y := Y) fixed.D1).homology n) :
    ((SelectedChainHomology.D2Iso n hn).hom.hom
      ((HomologicalComplex.homologyMap (SelectedUnderlyingHomology.tensorMap (Y := Y) g) n).hom x)).val =
      alpha (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) •
        ((SelectedChainHomology.D1Iso n hn).hom.hom x).val := by
  have h := congrArg (fun q => q.hom x) (SelectedUnderlyingHomology.arrow12 (Y := Y) a g hg n hn)
  change (SelectedChainHomology.D2Iso n hn).hom.hom
      ((HomologicalComplex.homologyMap (SelectedUnderlyingHomology.tensorMap (Y := Y) g) n).hom x) =
    (HAction (Y := Y) (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a)).hom
      ((SelectedChainHomology.D1Iso n hn).hom.hom x) at h
  exact (congrArg Subtype.val h).trans (HAction_val _ _)
end LittleFinitistic.SelectedChainAction

end

end OAI
