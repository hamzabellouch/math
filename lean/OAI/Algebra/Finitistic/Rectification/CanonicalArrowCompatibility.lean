import OAI.Algebra.Finitistic.Localization.NativeArrowBridge
import OAI.Algebra.Finitistic.Rectification.VertexHomotopyEquivalence

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace LittleFinitistic.CanonicalArrowCompatibility
open ExternalTensor.Section4 ExternalTensor.Section4.ArrowVertex
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

lemma diagonal_original (i : Fin 3) (D : RightComplex (B P)) :
    (VertexColumnComplex.diagonalComplexIso (composition P) i D).hom =
      diagonalComplex k (B P) (ThreeVertexAlgebra.vertex (composition P) i)
        ((ThreeVertexAlgebra.directedSystem (composition P)).idem i) D := by
  apply NativeBridge.diagonal_eq_of_original
  intro n x
  exact VertexColumnModels.diagonal_symm_val (composition P) (D.X n) i x

variable (D₀ D₁ D₂ : RightComplex (B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

lemma arrow01_target (a : Fin (d+1)) :
    ThreeVertexAlgebra.vertex (composition P) 1 * arrow01 P a = arrow01 P a := by
  change ThreeVertexAlgebra.mul (composition P) (0,1,0,0,0,0) (0,0,0,basis a,0,0) = _
  simp [ThreeVertexAlgebra.mul, arrow01]

lemma arrow12_target (b : Fin (d+1)) :
    ThreeVertexAlgebra.vertex (composition P) 2 * arrow12 P b = arrow12 P b := by
  change ThreeVertexAlgebra.mul (composition P) (0,0,1,0,0,0) (0,0,0,0,basis b,0) = _
  simp [ThreeVertexAlgebra.mul, arrow12]

/-- Left multiplication by the original first arrow on the actual vertex complexes. -/
def arrow01Map (a : Fin (d+1)) :=
  arrowComplex k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
    (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a) (arrow01_target P a)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)

/-- Left multiplication by the original second arrow on the actual vertex complexes. -/
def arrow12Map (b : Fin (d+1)) :=
  arrowComplex k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
    (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b) (arrow12_target P b)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)

/-- The homotopy uses exactly the original first and second vertex equivalences. -/
def compatibility01 (a : Fin (d+1)) : Homotopy
    (FirstVertex.iota P D₀ D₁ D₂ f g H ≫ arrow01Map P D₀ D₁ D₂ f g H a)
    (f a ≫ SecondVertex.iota P D₀ D₁ D₂ f g H) := by
  rw [FirstVertex.iota, SecondVertex.iota_original,
    diagonal_original, diagonal_original]
  exact NativeBridge.nativeCompatibility01 (ConcreteQuadraticDiagram.quadratic P)
    D₀ D₁ D₂ f g H ((ThreeVertexAlgebra.directedSystem (composition P)).idem 0)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1) a (arrow01_target P a)

/-- The homotopy uses exactly the original second and third vertex equivalences. -/
def compatibility12 (b : Fin (d+1)) : Homotopy
    (SecondVertex.iota P D₀ D₁ D₂ f g H ≫ arrow12Map P D₀ D₁ D₂ f g H b)
    (g b ≫ ThirdVertex.iota P D₀ D₁ D₂ f g H) := by
  rw [SecondVertex.iota_original, ThirdVertex.iota_original,
    diagonal_original, diagonal_original]
  exact NativeBridge.nativeCompatibility12 (ConcreteQuadraticDiagram.quadratic P)
    D₀ D₁ D₂ f g H ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem 2) b (arrow12_target P b)
end LittleFinitistic.CanonicalArrowCompatibility

end

end OAI
