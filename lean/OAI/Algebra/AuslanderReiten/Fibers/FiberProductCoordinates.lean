import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberRow
import OAI.Algebra.AuslanderReiten.Fibers.FiberSequenceCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R₀" => A k q
local notation "X₀" => simpleHomotopyObject q
local notation "τ₀" => AFrobeniusTrace k q
local notation "T₀" => fiberProductTriangle q H₁ H₂
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

theorem fiberProductFirst_coordinates (n : ℤ) (v : FiberHom q H₁ H₂ n) :
    fiberProductMiddleEquiv q H₁ H₂ n
      (TriangleGradedSequence.first k T₀ X₀ n v) = fiberHomRhoPair q H₁ H₂ n v := by
  erw [TriangleGradedSequence.first_eq_shift]
  apply Prod.ext
  · change (v ≫ (T₀).mor₁⟦n⟧') ≫ biprod.fst⟦n⟧' =
      v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₁ q H₁ H₂)))⟦n⟧'
    erw [Category.assoc, ← Functor.map_comp, fiberProductTriangle_first_fst]
  · change (v ≫ (T₀).mor₁⟦n⟧') ≫ biprod.snd⟦n⟧' =
      v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₂ q H₁ H₂)))⟦n⟧'
    erw [Category.assoc, ← Functor.map_comp, fiberProductTriangle_first_snd]

theorem fiberRhoPair_bijective_of_productFirst (n : ℤ)
    (hf : Function.Bijective (TriangleGradedSequence.first k T₀ X₀ n)) :
    Function.Bijective (fiberHomRhoPair q H₁ H₂ n) := by
  have he : (fiberHomRhoPair q H₁ H₂ n : FiberHom q H₁ H₂ n → _) =
      (fiberProductMiddleEquiv q H₁ H₂ n) ∘ (TriangleGradedSequence.first k T₀ X₀ n) := by
    funext v
    exact (fiberProductFirst_coordinates q H₁ H₂ n v).symm
  rw [he]
  exact (fiberProductMiddleEquiv q H₁ H₂ n).bijective.comp hf

end ArExplicit.T

end

end OAI
