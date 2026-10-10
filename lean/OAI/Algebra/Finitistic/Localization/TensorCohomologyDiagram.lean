import OAI.Algebra.Finitistic.Rectification.FullTensorRectification

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.TensorCohomologyDiagram
open ExternalTensor.Section4 QuadraticEncoding FullTensorRectification
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module (B P) N]

/-- From cohomology of an evaluated representative to the actual vertex of
cohomology of the full B-module tensor complex. -/
def comparison (v : Fin 3) (n : ℤ) : (source P D₀ D₁ D₂ N v).homology n ⟶
    (LeftVertexHomology.vertex k (B P) (ThreeVertexAlgebra.vertex (composition P) v)).obj
      ((tensor P D₀ D₁ D₂ f g H N).homology n) :=
  homologyMap (iota P D₀ D₁ D₂ f g H N v) n ≫
    (VertexHomology.iso (algebraMap k (B P)) (ThreeVertexAlgebra.vertex (composition P) v)
      ((ThreeVertexAlgebra.directedSystem (composition P)).idem v)
      (LeftVertexHomology.scalar_commute k (B P) _) (tensor P D₀ D₁ D₂ f g H N) n).hom

/-- The canonical cohomology comparison is invertible under the proved input hypotheses. -/
theorem comparison_isIso (v : Fin 3) (n lo hi : ℤ)
    (b₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (b₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (b₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n))
    (p₀ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₀.X n))
    (p₁ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₁.X n))
    (p₂ : ∀ n, Module.Projective (B P)ᵐᵒᵖ (D₂.X n)) :
    IsIso (comparison P D₀ D₁ D₂ f g H N v n) := by
  obtain ⟨E,hE⟩ := FullTensorRectification.equivalence P D₀ D₁ D₂ f g H N
    v lo hi b₀ b₁ b₂ p₀ p₁ p₂
  have : IsIso (homologyMap (iota P D₀ D₁ D₂ f g H N v) n) := by
    rw [← hE]
    exact (E.toHomologyIso n).isIso_hom
  unfold comparison
  infer_instance

/-- The first-family cohomology square retains the full original arrow action. -/
theorem arrow01_square (a : Fin (d+1)) (n : ℤ) :
    homologyMap (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (f a)) n ≫
      comparison P D₀ D₁ D₂ f g H N 1 n =
    comparison P D₀ D₁ D₂ f g H N 0 n ≫
      (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
        (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
        (CanonicalArrowCompatibility.arrow01_target P a)).app
          ((tensor P D₀ D₁ D₂ f g H N).homology n) := by
  have h := (FullTensorRectification.compatibility01 P D₀ D₁ D₂ f g H N a).homologyMap_eq n
  erw [homologyMap_comp (iota P D₀ D₁ D₂ f g H N 0)
      (arrow01Map P D₀ D₁ D₂ f g H N a) n,
    homologyMap_comp (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (f a))
      (iota P D₀ D₁ D₂ f g H N 1) n] at h
  dsimp only [comparison]
  erw [← Category.assoc, ← h, Category.assoc]
  erw [LeftVertexHomology.arrow_homology]
  exact (Category.assoc _ _ _).symm

/-- The second-family cohomology square retains the full original arrow action. -/
theorem arrow12_square (b : Fin (d+1)) (n : ℤ) :
    homologyMap (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (g b)) n ≫
      comparison P D₀ D₁ D₂ f g H N 2 n =
    comparison P D₀ D₁ D₂ f g H N 1 n ≫
      (LeftVertexHomology.arrow k (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
        (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
        (CanonicalArrowCompatibility.arrow12_target P b)).app
          ((tensor P D₀ D₁ D₂ f g H N).homology n) := by
  have h := (FullTensorRectification.compatibility12 P D₀ D₁ D₂ f g H N b).homologyMap_eq n
  erw [homologyMap_comp (iota P D₀ D₁ D₂ f g H N 1)
      (arrow12Map P D₀ D₁ D₂ f g H N b) n,
    homologyMap_comp (((BalancedTensor.tensorFunctor k (B P) N).mapHomologicalComplex (.up ℤ)).map (g b))
      (iota P D₀ D₁ D₂ f g H N 2) n] at h
  dsimp only [comparison]
  erw [← Category.assoc, ← h, Category.assoc]
  erw [LeftVertexHomology.arrow_homology]
  exact (Category.assoc _ _ _).symm
end LittleFinitistic.TensorCohomologyDiagram

end

end OAI
