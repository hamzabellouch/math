import OAI.Algebra.Finitistic.Localization.UnderlyingRepresentatives
import OAI.Algebra.Finitistic.Selected.SelectedChainDiagram

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedTensorComparison
open QuadraticEncoding FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

abbrev tensor (D : SourceVerdier.K P) :=
  ((BalancedTensor.tensorFunctor k (B P) X.Evaluation).mapHomologicalComplex (.up ℤ)).obj
    (UnderlyingRepresentatives.complex P D)

/-- The chosen representative's actual tensor is the source evaluation object. -/
def homotopyIso (D : SourceVerdier.K P) :
    (HomotopyCategory.quotient _ _).obj (tensor X D) ≅ (SourceEvaluation.evaluation X).obj D :=
  Iso.refl _

variable [FiniteDimensional k Y]
def finiteIso (D : SourceVerdier.K P) :
    (HomotopyCategory.quotient _ _).obj (tensor X D) ≅
      (inclusion k).obj ((SourceEvaluation.finite X).obj D) := Iso.refl _

abbrev tensorMap {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E) :=
  ((BalancedTensor.tensorFunctor k (B P) X.Evaluation).mapHomologicalComplex (.up ℤ)).map
    (((UnderlyingRepresentatives.forget P).mapHomologicalComplex (.up ℤ)).map f)

lemma map_comparison {D E : SourceVerdier.K P}
    (f : ConcreteChainRepresentatives.representative P D ⟶
      ConcreteChainRepresentatives.representative P E)
    (a : D ⟶ E)
    (ha : (HomotopyCategory.quotient _ _).map f = a.hom) :
    (HomotopyCategory.quotient _ _).map (tensorMap X f) ≫ (finiteIso X E).hom =
      (finiteIso X D).hom ≫ (inclusion k).map ((SourceEvaluation.finite X).map a) := by
  dsimp only [finiteIso,Iso.refl_hom]
  erw [Category.comp_id,Category.id_comp]
  change _ = ((BalancedTensor.tensorFunctor k (B P) X.Evaluation).mapHomotopyCategory (.up ℤ)).map
    (((UnderlyingRepresentatives.forget P).mapHomotopyCategory (.up ℤ)).map a.hom)
  erw [← ha,Functor.mapHomotopyCategory_map,Functor.mapHomotopyCategory_map]
end LittleFinitistic.SelectedTensorComparison

end

end OAI
