import OAI.Algebra.Finitistic.Rectification.TensorArrowComparison
import OAI.Algebra.Finitistic.Rectification.CanonicalArrowCompatibility

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.FullTensorRectification
open ExternalTensor.Section4 QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B P) N]

/-- The actual left B-module complex P tensor_B N. -/
abbrev tensor := ((BimoduleBalancedTensor.functor k (B P) N).mapHomologicalComplex (.up ℤ)).obj
  (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)

abbrev source (v : Fin 3) :=
  ((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).obj
    (VertexHomotopyEquivalence.source P D₀ D₁ D₂ v)
abbrev target (v : Fin 3) :=
  ((LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) v)).mapHomologicalComplex
    (.up ℤ)).obj (tensor P D₀ D₁ D₂ f g H N)

/-- The original vertex insertion after balanced tensoring and the canonical comparison. -/
def iota (v : Fin 3) : source P D₀ D₁ D₂ N v ⟶ target P D₀ D₁ D₂ f g H N v :=
  ((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map
    (VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H v) ≫
  (TensorArrowComparison.complexIso k (B P) N (ThreeVertexAlgebra.vertex (composition P) v)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem v)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).hom

/-- The equivalences retain the full left B-valued tensor target and the exact original maps. -/
theorem equivalence (v : Fin 3) (lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (p₀ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₀.X n))
    (p₁ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₁.X n))
    (p₂ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₂.X n)) :
    ∃ E : HomotopyEquiv (source P D₀ D₁ D₂ N v) (target P D₀ D₁ D₂ f g H N v),
      E.hom = iota P D₀ D₁ D₂ f g H N v := by
  obtain ⟨j,⟨h₁⟩,⟨h₂⟩⟩ := VertexHomotopyEquivalence.homotopy_inverse P D₀ D₁ D₂ f g H
    v lo hi b₀ b₁ b₂ p₀ p₁ p₂
  let E : HomotopyEquiv (VertexHomotopyEquivalence.source P D₀ D₁ D₂ v)
      (VertexHomotopyEquivalence.target P D₀ D₁ D₂ f g H v) :=
    ⟨VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H v,j,h₁,h₂⟩
  exact ⟨((BalancedTensor.tensorFunctor k (B P) N).mapHomotopyEquiv E).trans
    (HomotopyEquiv.ofIso (TensorArrowComparison.complexIso k (B P) N
      (ThreeVertexAlgebra.vertex (composition P) v)
      ((ThreeVertexAlgebra.directedSystem (composition P)).idem v)
      (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H))),rfl⟩

abbrev arrow01Map (a : Fin (d+1)) :=
  ((LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
    (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
    (CanonicalArrowCompatibility.arrow01_target P a)).mapHomologicalComplex (.up ℤ)).app
      (tensor P D₀ D₁ D₂ f g H N)
abbrev arrow12Map (b : Fin (d+1)) :=
  ((LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
    (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
    (CanonicalArrowCompatibility.arrow12_target P b)).mapHomologicalComplex (.up ℤ)).app
      (tensor P D₀ D₁ D₂ f g H N)

lemma original_iota0 : VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H 0 =
    FirstVertex.iota P D₀ D₁ D₂ f g H := by rfl
lemma original_iota1 : VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H 1 =
    SecondVertex.iota P D₀ D₁ D₂ f g H := by rfl
lemma original_iota2 : VertexHomotopyEquivalence.iota P D₀ D₁ D₂ f g H 2 =
    ThirdVertex.iota P D₀ D₁ D₂ f g H := by rfl

/-- Actual arrow compatibility on the vertex diagram of the full B-valued tensor. -/
def compatibility01 (a : Fin (d+1)) : Homotopy
    (iota P D₀ D₁ D₂ f g H N 0 ≫ arrow01Map P D₀ D₁ D₂ f g H N a)
    (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (f a) ≫
      iota P D₀ D₁ D₂ f g H N 1) := by
  have h := ((BalancedTensor.tensorFunctor k (B P) N).mapHomotopy
    (CanonicalArrowCompatibility.compatibility01 P D₀ D₁ D₂ f g H a)).compRight
      (TensorArrowComparison.complexIso k (B P) N (ThreeVertexAlgebra.vertex (composition P) 1)
        ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1)
        (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).hom
  erw [Functor.map_comp_assoc _ (FirstVertex.iota P D₀ D₁ D₂ f g H)
      (CanonicalArrowCompatibility.arrow01Map P D₀ D₁ D₂ f g H a),
    Functor.map_comp_assoc _ (f a) (SecondVertex.iota P D₀ D₁ D₂ f g H)] at h
  have hs := TensorArrowComparison.complex_arrow_square k (B P) N
    (ThreeVertexAlgebra.vertex (composition P) 0) (ThreeVertexAlgebra.vertex (composition P) 1)
    (arrow01 P a) ((ThreeVertexAlgebra.directedSystem (composition P)).idem 0)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1)
    (CanonicalArrowCompatibility.arrow01_target P a)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)
  erw [hs] at h
  dsimp only [iota]
  erw [original_iota0, original_iota1, Category.assoc]
  exact h

/-- The second arrow family retains its original maps as well. -/
def compatibility12 (b : Fin (d+1)) : Homotopy
    (iota P D₀ D₁ D₂ f g H N 1 ≫ arrow12Map P D₀ D₁ D₂ f g H N b)
    (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (g b) ≫
      iota P D₀ D₁ D₂ f g H N 2) := by
  have h := ((BalancedTensor.tensorFunctor k (B P) N).mapHomotopy
    (CanonicalArrowCompatibility.compatibility12 P D₀ D₁ D₂ f g H b)).compRight
      (TensorArrowComparison.complexIso k (B P) N (ThreeVertexAlgebra.vertex (composition P) 2)
        ((ThreeVertexAlgebra.directedSystem (composition P)).idem 2)
        (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)).hom
  erw [Functor.map_comp_assoc _ (SecondVertex.iota P D₀ D₁ D₂ f g H)
      (CanonicalArrowCompatibility.arrow12Map P D₀ D₁ D₂ f g H b),
    Functor.map_comp_assoc _ (g b) (ThirdVertex.iota P D₀ D₁ D₂ f g H)] at h
  have hs := TensorArrowComparison.complex_arrow_square k (B P) N
    (ThreeVertexAlgebra.vertex (composition P) 1) (ThreeVertexAlgebra.vertex (composition P) 2)
    (arrow12 P b) ((ThreeVertexAlgebra.directedSystem (composition P)).idem 1)
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem 2)
    (CanonicalArrowCompatibility.arrow12_target P b)
    (InducedRectification.total (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g H)
  erw [hs] at h
  dsimp only [iota]
  erw [original_iota1, original_iota2, Category.assoc]
  exact h
end LittleFinitistic.FullTensorRectification

end

end OAI
