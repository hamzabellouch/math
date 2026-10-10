import Mathlib

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
def cylinder (R : ℝ) : Set (V × ℝ) :=
  {p | ‖p.1‖<R ∧ -(R^4)<p.2 ∧ p.2≤0}

def pdist (p q : V × ℝ) : ℝ := ‖p.1-q.1‖+|p.2-q.2|^((1:ℝ)/4)

def HolderBound {E : Type*} [NormedAddCommGroup E] (α : ℝ) (Ω : Set (V × ℝ))
    (f : V × ℝ → E) (K : ℝ) : Prop :=
  (∀ p ∈ Ω, ‖f p‖≤K) ∧
  (∀ p ∈ Ω, ∀ q ∈ Ω, ‖f p-f q‖≤K*pdist p q^α)
def JetBound (α : ℝ) (Ω : Set (V × ℝ)) (u ut : ℝ → V → ℂ) (K : ℝ) : Prop :=
  (∀ j : ℕ, j≤4 → HolderBound α Ω (fun p => iteratedFDeriv ℝ j (u p.2) p.1) K) ∧
  HolderBound α Ω (fun p => ut p.2 p.1) K
end ParabolicInterior

end

end OAI
