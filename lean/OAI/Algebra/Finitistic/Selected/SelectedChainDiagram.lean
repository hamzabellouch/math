import OAI.Algebra.Finitistic.Localization.ConcreteChainRepresentatives
import OAI.Algebra.Finitistic.Selected.SelectedNativeAction

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedChainDiagram
open SelectedFixedDiagram RelationBasisCoefficients ConcreteChainRepresentatives

abbrev D0 := representative P fixed.D0
abbrev D1 := representative P fixed.D1
abbrev D2 := representative P fixed.D2

/-- Chain representatives and all specified relation homotopies for the one fixed diagram. -/
structure Data where
  f : Fin (encoding.generators+1) → (D0 ⟶ D1)
  g : Fin (encoding.generators+1) → (D1 ⟶ D2)
  f_quotient : ∀ a, (HomotopyCategory.quotient (SourceVerdier.Proj P) (.up ℤ)).map (f a) = (fixed.f a).hom
  g_quotient : ∀ b, (HomotopyCategory.quotient (SourceVerdier.Proj P) (.up ℤ)).map (g b) = (fixed.g b).hom
  homotopy : ∀ r : RelationIndex P,
    Homotopy (∑ a, ∑ b, basisCoefficient P r a b • (f a ≫ g b)) 0

/-- These choices, too, are made once before any evaluation module Y. -/
def fixedChain : Data := Classical.choice (by
  obtain ⟨f,g,hf,hg,⟨h⟩⟩ := quadratic_representatives P _ _ _
    fixed.D0 fixed.D1 fixed.D2 fixed.f fixed.g (basisCoefficient P) fixed.relations
  exact ⟨⟨f,g,hf,hg,h⟩⟩)

theorem bounded : BoundedHomotopy.boundedComplex (SourceVerdier.Proj P) D0 ∧
    BoundedHomotopy.boundedComplex (SourceVerdier.Proj P) D1 ∧
    BoundedHomotopy.boundedComplex (SourceVerdier.Proj P) D2 :=
  ⟨representative_bounded P fixed.D0,representative_bounded P fixed.D1,representative_bounded P fixed.D2⟩

def fK (a : Fin (encoding.generators+1)) : fixed.D0 ⟶ fixed.D1 :=
  ObjectProperty.homMk ((HomotopyCategory.quotient (SourceVerdier.Proj P) (.up ℤ)).map (fixedChain.f a))
def gK (b : Fin (encoding.generators+1)) : fixed.D1 ⟶ fixed.D2 :=
  ObjectProperty.homMk ((HomotopyCategory.quotient (SourceVerdier.Proj P) (.up ℤ)).map (fixedChain.g b))

theorem fK_eq (a : Fin (encoding.generators+1)) : fK a = fixed.f a := by
  apply ObjectProperty.hom_ext
  exact fixedChain.f_quotient a

theorem gK_eq (b : Fin (encoding.generators+1)) : gK b = fixed.g b := by
  apply ObjectProperty.hom_ext
  exact fixedChain.g_quotient b

universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

theorem evaluated_f (a : Fin (encoding.generators+1)) :
    (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).map (fK a) ≫
      (SelectedNativeEvaluation.D1Iso (Y := Y)).hom =
    (SelectedNativeEvaluation.D0Iso (Y := Y)).hom ≫ SelectedNativeEvaluation.targetAction (Y := Y)
      (RelationBasisAction.arrow (SelectionEncoding.generator encoding) a) := by
  rw [fK_eq]
  exact SelectedNativeEvaluation.D_arrow01 a

theorem evaluated_g (b : Fin (encoding.generators+1)) :
    (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).map (gK b) ≫
      (SelectedNativeEvaluation.D2Iso (Y := Y)).hom =
    (SelectedNativeEvaluation.D1Iso (Y := Y)).hom ≫ SelectedNativeEvaluation.targetAction (Y := Y)
      (RelationBasisAction.arrow (SelectionEncoding.generator encoding) b) := by
  rw [gK_eq]
  exact SelectedNativeEvaluation.D_arrow12 b
end LittleFinitistic.SelectedChainDiagram

end

end OAI
