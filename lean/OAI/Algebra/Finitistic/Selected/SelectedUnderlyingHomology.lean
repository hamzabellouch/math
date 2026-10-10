import OAI.Algebra.Finitistic.Selected.SelectedChainHomology

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedUnderlyingHomology
open QuadraticEncoding SelectedFixedDiagram SelectedNativeEvaluation SelectedTargetHomology
open SelectedChainHomology
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

/-- Tensor an actual map of the underlying right-module complexes. -/
abbrev tensorMap {D E : SourceVerdier.K P}
    (f : UnderlyingRepresentatives.complex P D ⟶ UnderlyingRepresentatives.complex P E) :=
  ((BalancedTensor.tensorFunctor ℂ (B P) (representation (Y := Y)).Evaluation).mapHomologicalComplex
    (.up ℤ)).map f

lemma derived_map {D E : SourceVerdier.K P}
    (f : UnderlyingRepresentatives.complex P D ⟶ UnderlyingRepresentatives.complex P E)
    (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = (SourceModelBridge.ambient P).map a) :
    DerivedCategory.Q.map (tensorMap (Y := Y) f) ≫ (derivedIso (Y := Y) E).hom =
      (derivedIso (Y := Y) D).hom ≫ I.map ((source (Y := Y)).map a) := by
  have hq : (HomotopyCategory.quotient _ _).map (tensorMap (Y := Y) f) =
      (FiniteProjectiveHomotopy.inclusion ℂ).map
        ((SourceEvaluation.finite (representation (Y := Y))).map a) := by
    change _ = ((BalancedTensor.tensorFunctor ℂ (B P)
      (representation (Y := Y)).Evaluation).mapHomotopyCategory (.up ℤ)).map
        ((SourceModelBridge.ambient P).map a)
    rw [← ha,Functor.mapHomotopyCategory_map]
  have h : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (tensorMap (Y := Y) f)) ≫
      DerivedCategory.Qh.map (SelectedTensorComparison.finiteIso (representation (Y := Y)) E).hom =
    DerivedCategory.Qh.map (SelectedTensorComparison.finiteIso (representation (Y := Y)) D).hom ≫
      I.map ((source (Y := Y)).map a) := by
    dsimp only [SelectedTensorComparison.finiteIso,Iso.refl_hom]
    erw [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id,Category.comp_id,Category.id_comp,hq]
    rfl
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.quotientCompQhIso C).symm.app (complex (Y := Y) D))
    ((DerivedCategory.quotientCompQhIso C).symm.app (complex (Y := Y) E))
    (DerivedCategory.Qh.mapIso (SelectedTensorComparison.finiteIso (representation (Y := Y)) D))
    (DerivedCategory.Qh.mapIso (SelectedTensorComparison.finiteIso (representation (Y := Y)) E))
    ((DerivedCategory.quotientCompQhIso C).inv.naturality (tensorMap (Y := Y) f)) h

lemma comparison_map {D E : SourceVerdier.K P}
    (f : UnderlyingRepresentatives.complex P D ⟶ UnderlyingRepresentatives.complex P E)
    (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = (SourceModelBridge.ambient P).map a) (n : ℤ) :
    HomologicalComplex.homologyMap (tensorMap (Y := Y) f) n ≫ (comparison (Y := Y) E n).hom =
      (comparison (Y := Y) D n).hom ≫ (cohomology n).map ((source (Y := Y)).map a) := by
  have h := congrArg (DerivedCategory.homologyFunctor C n).map (derived_map (Y := Y) f a ha)
  simp only [Functor.map_comp] at h
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.homologyFunctorFactors C n).symm.app (complex (Y := Y) D))
    ((DerivedCategory.homologyFunctorFactors C n).symm.app (complex (Y := Y) E))
    ((DerivedCategory.homologyFunctor C n).mapIso (derivedIso (Y := Y) D))
    ((DerivedCategory.homologyFunctor C n).mapIso (derivedIso (Y := Y) E))
    ((DerivedCategory.homologyFunctorFactors C n).inv.naturality (tensorMap (Y := Y) f)) h

lemma homology_arrow {D E : SourceVerdier.K P}
    (f : UnderlyingRepresentatives.complex P D ⟶ UnderlyingRepresentatives.complex P E)
    (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = (SourceModelBridge.ambient P).map a)
    (eD : (source (Y := Y)).obj D ≅ target (Y := Y))
    (eE : (source (Y := Y)).obj E ≅ target (Y := Y)) (r : SelectionRing)
    (hs : (source (Y := Y)).map a ≫ eE.hom = eD.hom ≫ targetAction (Y := Y) r)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (Y := Y) f) n ≫ (homologyIso E eE n hn).hom =
      (homologyIso D eD n hn).hom ≫ HAction (Y := Y) r := by
  have h := congrArg (cohomology n).map hs
  simp only [Functor.map_comp] at h
  exact DiagramEvaluationSquares.compose _ _ _
    (comparison D n) (comparison E n)
    ((cohomology n).mapIso eD ≪≫ modelIso n hn)
    ((cohomology n).mapIso eE ≪≫ modelIso n hn)
    (comparison_map f a ha n)
    (DiagramEvaluationSquares.compose _ _ _ ((cohomology n).mapIso eD)
      ((cohomology n).mapIso eE) (modelIso n hn) (modelIso n hn) h (model_action n hn r))

lemma arrow01 (a : Fin (encoding.generators+1))
    (f : UnderlyingRepresentatives.complex P fixed.D0 ⟶ UnderlyingRepresentatives.complex P fixed.D1)
    (hf : (HomotopyCategory.quotient _ _).map f = (SourceModelBridge.ambient P).map (fixed.f a))
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (Y := Y) f) n ≫ (SelectedChainHomology.D1Iso n hn).hom =
      (SelectedChainHomology.D0Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  homology_arrow f (fixed.f a) hf SelectedNativeEvaluation.D0Iso SelectedNativeEvaluation.D1Iso _
    (SelectedNativeEvaluation.D_arrow01 a) n hn
lemma arrow12 (a : Fin (encoding.generators+1))
    (g : UnderlyingRepresentatives.complex P fixed.D1 ⟶ UnderlyingRepresentatives.complex P fixed.D2)
    (hg : (HomotopyCategory.quotient _ _).map g = (SourceModelBridge.ambient P).map (fixed.g a))
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (Y := Y) g) n ≫ (SelectedChainHomology.D2Iso n hn).hom =
      (SelectedChainHomology.D1Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  homology_arrow g (fixed.g a) hg SelectedNativeEvaluation.D1Iso SelectedNativeEvaluation.D2Iso _
    (SelectedNativeEvaluation.D_arrow12 a) n hn
end LittleFinitistic.SelectedUnderlyingHomology

end

end OAI
