import OAI.Algebra.Finitistic.Localization.QuotientRelations
import Mathlib.Algebra.Module.ULift

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
open BalancedTensor FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

abbrev liftedY := ULift.{u} Y

def liftedVertexEquiv (i : Fin 3) :
    (tensorFunctor k (B P) X.Evaluation).obj (vertexModule P i) ≃ₗ[k] ULift.{u} Y :=
  (evaluationVertexEquiv X i).trans ULift.moduleEquiv.symm

def actionArrow (h : Fin (d+1)) : ModuleCat.of k (ULift.{u} Y) ⟶ ModuleCat.of k (ULift.{u} Y) :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    ((Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator h).comp
      ULift.moduleEquiv.toLinearMap))

lemma tensor_arrow01_square (h : Fin (d+1)) :
    (tensorFunctor k (B P) X.Evaluation).map (arrowModule01 P h) ≫
      (liftedVertexEquiv X 1).toModuleIso.hom =
    (liftedVertexEquiv X 0).toModuleIso.hom ≫ actionArrow X h := by
  ext z
  have h := evaluation_arrow01 X h (evaluationVertexEquiv X 0 z)
  simpa [liftedVertexEquiv, actionArrow] using h

lemma tensor_arrow12_square (h : Fin (d+1)) :
    (tensorFunctor k (B P) X.Evaluation).map (arrowModule12 P h) ≫
      (liftedVertexEquiv X 2).toModuleIso.hom =
    (liftedVertexEquiv X 1).toModuleIso.hom ≫ actionArrow X h := by
  ext z
  have h := evaluation_arrow12 X h (evaluationVertexEquiv X 1 z)
  simpa [liftedVertexEquiv, actionArrow] using h

abbrev vectorStalk := HomotopyCategory.singleFunctor (ModuleCat.{max u v} k) 0

/-- Evaluation of each concrete degree-zero vertex object is the stalk complex Y. -/
def homotopyVertexIso (i : Fin 3) :
    (boundedEvaluation X).obj (vertexK P i) ≅ (vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y)) :=
  (HomotopyCategory.quotient _ _).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex
      (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).app (vertexModule P i)) ≪≫
  (vectorStalk (k := k)).mapIso (liftedVertexEquiv X i).toModuleIso

lemma homotopy_arrow01_square (h : Fin (d+1)) :
    (boundedEvaluation X).map (arrowK01 P h) ≫ (homotopyVertexIso X 1).hom =
    (homotopyVertexIso X 0).hom ≫ (vectorStalk (k := k)).map (actionArrow X h) := by
  change (homotopyEvaluation k (B P) X.Evaluation).map
    ((inclusion (B P)ᵐᵒᵖ).map (arrowK01 P h)) ≫ _ = _
  unfold arrowK01
  erw [Functor.map_preimage]
  change ((tensorFunctor k (B P) X.Evaluation).mapHomotopyCategory (.up ℤ)).map
    ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule01 P h))) ≫
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 1)) ≫
      (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (liftedVertexEquiv X 1).toModuleIso.hom)) =
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 0)) ≫
      (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (liftedVertexEquiv X 0).toModuleIso.hom)) ≫
    (HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (actionArrow X h))
  simp only [Functor.mapHomotopyCategory_map]
  have hn := (HomologicalComplex.singleMapHomologicalComplex
    (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.naturality (arrowModule01 P h)
  have hm := congrArg (fun f => (HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map f)
    (tensor_arrow01_square X h)
  simp only [Functor.map_comp] at hm
  have hc := (congrArg (fun f => f ≫
    (HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map
      (liftedVertexEquiv X 1).toModuleIso.hom) hn).trans (by
        simpa only [Category.assoc, Functor.comp_map, degreeZero] using congrArg (fun f =>
          (HomologicalComplex.singleMapHomologicalComplex
            (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 0) ≫ f) hm)
  simpa only [Functor.map_comp, Category.assoc, Functor.comp_map, degreeZero] using
    congrArg (fun f => (HomotopyCategory.quotient (ModuleCat.{max u v} k) (.up ℤ)).map f) hc

lemma homotopy_arrow12_square (h : Fin (d+1)) :
    (boundedEvaluation X).map (arrowK12 P h) ≫ (homotopyVertexIso X 2).hom =
    (homotopyVertexIso X 1).hom ≫ (vectorStalk (k := k)).map (actionArrow X h) := by
  change (homotopyEvaluation k (B P) X.Evaluation).map
    ((inclusion (B P)ᵐᵒᵖ).map (arrowK12 P h)) ≫ _ = _
  unfold arrowK12
  erw [Functor.map_preimage]
  change ((tensorFunctor k (B P) X.Evaluation).mapHomotopyCategory (.up ℤ)).map
    ((HomotopyCategory.quotient _ _).map ((degreeZero P).map (arrowModule12 P h))) ≫
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 2)) ≫
      (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (liftedVertexEquiv X 2).toModuleIso.hom)) =
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 1)) ≫
      (HomotopyCategory.quotient _ _).map
        ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (liftedVertexEquiv X 1).toModuleIso.hom)) ≫
    (HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map (actionArrow X h))
  simp only [Functor.mapHomotopyCategory_map]
  have hn := (HomologicalComplex.singleMapHomologicalComplex
    (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.naturality (arrowModule12 P h)
  have hm := congrArg (fun f => (HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map f)
    (tensor_arrow12_square X h)
  simp only [Functor.map_comp] at hm
  have hc := (congrArg (fun f => f ≫
    (HomologicalComplex.single (ModuleCat.{max u v} k) (.up ℤ) (0 : ℤ)).map
      (liftedVertexEquiv X 2).toModuleIso.hom) hn).trans (by
        simpa only [Category.assoc, Functor.comp_map, degreeZero] using congrArg (fun f =>
          (HomologicalComplex.singleMapHomologicalComplex
            (tensorFunctor k (B P) X.Evaluation) (.up ℤ) (0 : ℤ)).hom.app (vertexModule P 1) ≫ f) hm)
  simpa only [Functor.map_comp, Category.assoc, Functor.comp_map, degreeZero] using
    congrArg (fun f => (HomotopyCategory.quotient (ModuleCat.{max u v} k) (.up ℤ)).map f) hc
end LittleFinitistic.QuadraticEncoding

end

end OAI
