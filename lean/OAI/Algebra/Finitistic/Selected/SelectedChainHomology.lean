import OAI.Algebra.Finitistic.Selected.SelectedTargetHomology

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedChainHomology
open QuadraticEncoding SelectedFixedDiagram SelectedNativeEvaluation SelectedTensorComparison
open SelectedTargetHomology
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]
abbrev representation := SourceActionEvaluation.representation (Y := Y) encoding
abbrev complex (D : SourceVerdier.K P) := tensor (representation (Y := Y)) D
abbrev source := SelectedDiagramEvaluation.sourceEvaluation (Y := Y)

def derivedIso (D : SourceVerdier.K P) :
    DerivedCategory.Q.obj (complex (Y := Y) D) ≅ I.obj ((source (Y := Y)).obj D) :=
  (DerivedCategory.quotientCompQhIso C).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso (finiteIso (representation (Y := Y)) D)

def comparison (D : SourceVerdier.K P) (n : ℤ) :
    (complex (Y := Y) D).homology n ≅ (cohomology n).obj ((source (Y := Y)).obj D) :=
  (DerivedCategory.homologyFunctorFactors C n).symm.app _ ≪≫
    (DerivedCategory.homologyFunctor C n).mapIso (derivedIso (Y := Y) D)

lemma derived_map {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E) (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) :
    DerivedCategory.Q.map (tensorMap (representation (Y := Y)) f) ≫
      (derivedIso (Y := Y) E).hom =
        (derivedIso (Y := Y) D).hom ≫ I.map ((source (Y := Y)).map a) := by
  have h := congrArg DerivedCategory.Qh.map (map_comparison (representation (Y := Y)) f a ha)
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.quotientCompQhIso C).inv.naturality
    (tensorMap (representation (Y := Y)) f)
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.quotientCompQhIso C).symm.app (complex (Y := Y) D))
    ((DerivedCategory.quotientCompQhIso C).symm.app (complex (Y := Y) E))
    (DerivedCategory.Qh.mapIso (finiteIso (representation (Y := Y)) D))
    (DerivedCategory.Qh.mapIso (finiteIso (representation (Y := Y)) E)) hn h

lemma comparison_map {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E) (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) (n : ℤ) :
    HomologicalComplex.homologyMap (tensorMap (representation (Y := Y)) f) n ≫
      (comparison (Y := Y) E n).hom =
        (comparison (Y := Y) D n).hom ≫ (cohomology n).map ((source (Y := Y)).map a) := by
  have h := congrArg (DerivedCategory.homologyFunctor C n).map (derived_map (Y := Y) f a ha)
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.homologyFunctorFactors C n).inv.naturality
    (tensorMap (representation (Y := Y)) f)
  exact DiagramEvaluationSquares.compose _ _ _
    ((DerivedCategory.homologyFunctorFactors C n).symm.app (complex (Y := Y) D))
    ((DerivedCategory.homologyFunctorFactors C n).symm.app (complex (Y := Y) E))
    ((DerivedCategory.homologyFunctor C n).mapIso (derivedIso (Y := Y) D))
    ((DerivedCategory.homologyFunctor C n).mapIso (derivedIso (Y := Y) E)) hn h

def modelIso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (cohomology n).obj (target (Y := Y)) ≅ H (Y := Y) := by
  by_cases h : n = 0
  · subst n; exact targetH0
  · have hm : n = -3 := hn.resolve_left h
    subst n; exact targetHm3

lemma model_action (n : ℤ) (hn : n = 0 ∨ n = -3) (r : SelectionRing) :
    (cohomology n).map (targetAction (Y := Y) r) ≫ (modelIso (Y := Y) n hn).hom =
      (modelIso (Y := Y) n hn).hom ≫ HAction (Y := Y) r := by
  rcases hn with rfl | rfl
  · exact targetH0_action r
  · exact targetHm3_action r

/-- Actual homology of a selected chain tensor, with its chosen target identification. -/
def homologyIso (D : SourceVerdier.K P)
    (e : (source (Y := Y)).obj D ≅ target (Y := Y))
    (n : ℤ) (hn : n = 0 ∨ n = -3) : (complex (Y := Y) D).homology n ≅ H (Y := Y) :=
  comparison D n ≪≫ (cohomology n).mapIso e ≪≫ modelIso n hn

lemma homology_zero (D : SourceVerdier.K P)
    (e : (source (Y := Y)).obj D ≅ target (Y := Y))
    (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) : IsZero ((complex (Y := Y) D).homology n) :=
  (comparison D n ≪≫ (cohomology n).mapIso e).isZero_iff.mpr (target_zero n h0 hm)

lemma homology_arrow {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E) (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom)
    (eD : (source (Y := Y)).obj D ≅ target (Y := Y))
    (eE : (source (Y := Y)).obj E ≅ target (Y := Y)) (r : SelectionRing)
    (hs : (source (Y := Y)).map a ≫ eE.hom = eD.hom ≫ targetAction (Y := Y) r)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (representation (Y := Y)) f) n ≫
      (homologyIso E eE n hn).hom =
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

/-- All three actual tensors have the primary H(Y) as homology in both selected degrees. -/
def D0Iso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (complex (Y := Y) fixed.D0).homology n ≅ H (Y := Y) :=
  homologyIso _ SelectedNativeEvaluation.D0Iso n hn
def D1Iso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (complex (Y := Y) fixed.D1).homology n ≅ H (Y := Y) :=
  homologyIso _ SelectedNativeEvaluation.D1Iso n hn
def D2Iso (n : ℤ) (hn : n = 0 ∨ n = -3) :
    (complex (Y := Y) fixed.D2).homology n ≅ H (Y := Y) :=
  homologyIso _ SelectedNativeEvaluation.D2Iso n hn

lemma D0_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((complex (Y := Y) fixed.D0).homology n) :=
  homology_zero _ SelectedNativeEvaluation.D0Iso n h0 hm
lemma D1_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((complex (Y := Y) fixed.D1).homology n) :=
  homology_zero _ SelectedNativeEvaluation.D1Iso n h0 hm
lemma D2_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((complex (Y := Y) fixed.D2).homology n) :=
  homology_zero _ SelectedNativeEvaluation.D2Iso n h0 hm

/-- This applies to any chain representative of the same fixed first arrow. -/
lemma arrow01 (a : Fin (encoding.generators+1))
    (f : SelectedChainDiagram.D0 ⟶ SelectedChainDiagram.D1)
    (hf : (HomotopyCategory.quotient _ _).map f = (fixed.f a).hom)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (representation (Y := Y)) f) n ≫ (D1Iso n hn).hom =
      (D0Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  homology_arrow f (fixed.f a) hf SelectedNativeEvaluation.D0Iso SelectedNativeEvaluation.D1Iso _
    (SelectedNativeEvaluation.D_arrow01 a) n hn

lemma arrow12 (a : Fin (encoding.generators+1))
    (g : SelectedChainDiagram.D1 ⟶ SelectedChainDiagram.D2)
    (hg : (HomotopyCategory.quotient _ _).map g = (fixed.g a).hom)
    (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap (tensorMap (representation (Y := Y)) g) n ≫ (D2Iso n hn).hom =
      (D1Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  homology_arrow g (fixed.g a) hg SelectedNativeEvaluation.D1Iso SelectedNativeEvaluation.D2Iso _
    (SelectedNativeEvaluation.D_arrow12 a) n hn

lemma fixed_arrow01 (a : Fin (encoding.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap
      (tensorMap (representation (Y := Y)) (SelectedChainDiagram.fixedChain.f a)) n ≫ (D1Iso n hn).hom =
      (D0Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  arrow01 a _ (SelectedChainDiagram.fixedChain.f_quotient a) n hn
lemma fixed_arrow12 (a : Fin (encoding.generators+1)) (n : ℤ) (hn : n = 0 ∨ n = -3) :
    HomologicalComplex.homologyMap
      (tensorMap (representation (Y := Y)) (SelectedChainDiagram.fixedChain.g a)) n ≫ (D2Iso n hn).hom =
      (D1Iso n hn).hom ≫ HAction (Y := Y)
        (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) :=
  arrow12 a _ (SelectedChainDiagram.fixedChain.g_quotient a) n hn
end LittleFinitistic.SelectedChainHomology

end

end OAI
