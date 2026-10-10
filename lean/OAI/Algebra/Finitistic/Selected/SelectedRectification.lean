import OAI.Algebra.Finitistic.Selected.SelectedChainDiagram
import OAI.Algebra.Finitistic.Rectification.RectificationLemma
import OAI.Algebra.Finitistic.Localization.UnderlyingRepresentatives

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SelectedRectification
open SelectedFixedDiagram ExternalTensor.Section4 RelationBasisCoefficients

abbrev D0 := UnderlyingRepresentatives.complex P fixed.D0
abbrev D1 := UnderlyingRepresentatives.complex P fixed.D1
abbrev D2 := UnderlyingRepresentatives.complex P fixed.D2
abbrev F := (UnderlyingRepresentatives.forget P).mapHomologicalComplex (.up ℤ)
def f (a : Fin (encoding.generators+1)) : D0 ⟶ D1 := F.map (SelectedChainDiagram.fixedChain.f a)
def g (b : Fin (encoding.generators+1)) : D1 ⟶ D2 := F.map (SelectedChainDiagram.fixedChain.g b)
def relations (r : RelationIndex P) :
    Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D0 D1 D2 f g r) 0 :=
  UnderlyingRepresentatives.relationHomotopy P (encoding.generators+1) (encoding.generators+1)
    (Module.finrank ℂ (QuadraticEncoding.relationSpace P)) fixed.D0 fixed.D1 fixed.D2
    SelectedChainDiagram.fixedChain.f SelectedChainDiagram.fixedChain.g (basisCoefficient P)
    SelectedChainDiagram.fixedChain.homotopy r

/-- One explicit bimodule complex chosen before any evaluation module. -/
def bimodule : BiComplex ℂ (QuadraticEncoding.B P) :=
  InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D0 D1 D2 f g relations

/-- The single fixed selecting complex satisfies the full rectification lemma,
including all original vertex and arrow maps, independently of Y. -/
theorem verified : ∃ lo hi : ℤ, RectificationLemma.Verified P D0 D1 D2 f g relations lo hi := by
  obtain ⟨l₀,h₀,b₀⟩ := UnderlyingRepresentatives.bounded P fixed.D0
  obtain ⟨l₁,h₁,b₁⟩ := UnderlyingRepresentatives.bounded P fixed.D1
  obtain ⟨l₂,h₂,b₂⟩ := UnderlyingRepresentatives.bounded P fixed.D2
  let lo := min l₀ (min l₁ l₂)
  let hi := max h₀ (max h₁ h₂)
  refine ⟨lo,hi,RectificationLemma.rectification P D0 D1 D2 f g relations lo hi
    (fun n hn => b₀ n ?_) (fun n hn => b₁ n ?_) (fun n hn => b₂ n ?_)
    (UnderlyingRepresentatives.projective P fixed.D0)
    (UnderlyingRepresentatives.projective P fixed.D1)
    (UnderlyingRepresentatives.projective P fixed.D2)
    (UnderlyingRepresentatives.finite P fixed.D0)
    (UnderlyingRepresentatives.finite P fixed.D1)
    (UnderlyingRepresentatives.finite P fixed.D2)⟩
  all_goals dsimp [lo,hi] at hn; omega
end LittleFinitistic.SelectedRectification

end

end OAI
