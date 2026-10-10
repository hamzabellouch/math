import OAI.Algebra.Finitistic.Encoding.RelationVertexSequence
import OAI.Algebra.Finitistic.Rectification.TotalInterchange
import OAI.Algebra.Finitistic.Rectification.GradedVertexAcyclic

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace LittleFinitistic.FinalGradedAcyclic
open QuadraticEncoding ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
open RectificationTotal
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
local notation "data" => Exactness.data s D₀ D₁ D₂ f g

/-- The original source-zero quotient at vertex two is acyclic, with every relation column retained. -/
theorem grade0_vertex2_acyclic :
    ((RelationVertexCoordinates.vertex P).obj (Exactness.G0 s D₀ D₁ D₂ f g)).Acyclic := by
  let F := BimoduleVertex.functor k T (ThreeVertexAlgebra.vertex (composition P) 2)
  let S := (RelationVertexSequence.originalSequence P D₀ D₁ D₂ f g).map
    (RelationVertexCoordinates.vertex P)
  have he : mapNullHomotopy F (p0 data) (q0 data) (h0 data) = Homotopy.ofEq S.zero := by
    ext i j
    simp [mapNullHomotopy_hom,h0,Homotopy.ofEq]
    rfl
  apply GradedVertexAcyclic.acyclic_of_iso
    (totalInterchange F (p0 data) (q0 data) (h0 data))
  rw [he]
  exact RectificationAcyclic.short_exact_total_acyclic S
    (RelationVertexSequence.shortExact P D₀ D₁ D₂ f g)
end LittleFinitistic.FinalGradedAcyclic

end

end OAI
