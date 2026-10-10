import OAI.Algebra.Finitistic.Rectification.VertexModuleAssembly
import OAI.Algebra.Finitistic.Encoding.EncodingLinearity
import OAI.Algebra.Finitistic.Rectification.CanonicalArrowCompatibility

namespace OAI
noncomputable section
namespace LittleFinitistic.EncodingModuleAssembly
open QuadraticEncoding VertexDecomposition VertexModuleAssembly
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module (B P) M] [Module (B P) N]
  [IsScalarTower k (B P) M] [IsScalarTower k (B P) N]

abbrev system := ThreeVertexAlgebra.directedSystem (composition P)

/-- Reconstruct a full module isomorphism from the three actual vertex-space
isomorphisms and the two finite arrow families. Its underlying vector-space map
is precisely the direct-sum assembly of the supplied vertex isomorphisms. -/
def equiv (E : ∀ i, Space (system P) M i ≃ₗ[k] Space (system P) N i)
    (h01 : ∀ a x, E 1 (arrow (system P) (i := 0) (j := 1) (arrow01 P a)
      (CanonicalArrowCompatibility.arrow01_target P a) x) =
      arrow (system P) (i := 0) (j := 1) (arrow01 P a)
        (CanonicalArrowCompatibility.arrow01_target P a) (E 0 x))
    (h12 : ∀ b x, E 2 (arrow (system P) (i := 1) (j := 2) (arrow12 P b)
      (CanonicalArrowCompatibility.arrow12_target P b) x) =
      arrow (system P) (i := 1) (j := 2) (arrow12 P b)
        (CanonicalArrowCompatibility.arrow12_target P b) (E 1 x)) : M ≃ₗ[B P] N :=
  EncodingLinearity.linearEquiv P (assembled (system P) E)
    (vertex_smul (system P) E)
    (fun a => arrow_smul (system P) E (arrow01 P a)
      (CanonicalArrowCompatibility.arrow01_target P a)
      ((ConcreteQuadraticDiagram.quadratic P).ha a) (h01 a))
    (fun b => arrow_smul (system P) E (arrow12 P b)
      (CanonicalArrowCompatibility.arrow12_target P b)
      ((ConcreteQuadraticDiagram.quadratic P).hb b) (h12 b))
end LittleFinitistic.EncodingModuleAssembly

end

end OAI
