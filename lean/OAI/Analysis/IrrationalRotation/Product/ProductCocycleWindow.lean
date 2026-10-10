import OAI.Analysis.IrrationalRotation.Rotation.CocycleWindowBounds
import OAI.Analysis.IrrationalRotation.Product.ProductCocycle

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp
namespace Invariant233.ProductCocycle

theorem finite_window_bounds {I : Type*} (s : Finset I)
    (θ c : I → ℝ) (K : ℕ) (x y : Space I)
    (hθ : ∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, representative (x i) + (K : ℝ) * θ i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * θ i ≤ representative (y i))
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    1 / cocycleVersion θ c v x ≤ Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
      cocycleVersion θ c (-v) y ≤ Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  exact CocycleWindowBounds.cocycle_bounds s
    (fun i => representative (x i)) (fun i => representative (y i)) θ c K
    (fun i => representative_mem_Ico (x i)) (fun i => representative_mem_Ico (y i))
    hθ hc hleft hright v hv

theorem finite_window_coefficients {I : Type*} (s : Finset I)
    (θ c : I → ℝ) (K : ℕ) (x y : Space I)
    (hθ : ∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, representative (x i) + (K : ℝ) * θ i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * θ i ≤ representative (y i))
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    (∀ v : ℤ, |v| ≤ (K : ℤ) →
      ‖ξ v / (cocycleVersion θ c v x : ℂ)‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i)) ∧
    (∀ v : ℤ, |v| ≤ (K : ℤ) →
      ‖(cocycleVersion θ c (-v) y : ℂ) * conj (γ (-v))‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i)) := by
  have h := fun v hv => CocycleWindowBounds.coefficient_bounds s
    (fun i => representative (x i)) (fun i => representative (y i)) θ c K
    (fun i => representative_mem_Ico (x i)) (fun i => representative_mem_Ico (y i))
    hθ hc hleft hright ξ γ hξ hγ v hv
  exact ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩

theorem central_coefficients {I Ω : Type*} (θ c : I → ℝ)
    (x y : Ω → Space I) (ξ γ : Ω → ℓ²(ℤ, ℂ)) (ω : Ω) :
    InvariantProjection.ConditionalConvolution.coeffA ξ
      (fun z v => cocycleVersion θ c v (x z)) ω 0 = ξ ω 0 ∧
    InvariantProjection.ConditionalConvolution.coeffB γ
      (fun z v => cocycleVersion θ c v (y z)) ω 0 = conj (γ ω 0) := by
  simp [InvariantProjection.ConditionalConvolution.coeffA,
    InvariantProjection.ConditionalConvolution.coeffB]

end Invariant233.ProductCocycle

end

end OAI
