import OAI.Analysis.WeakInfiniteness.TensorFoundations

namespace OAI

/-! Testing operators on tensor products of two total families of vectors. -/

noncomputable section
open scoped TensorProduct
open UniformSpace

namespace WeakPureInfiniteness

variable {H K E I J : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem completed_tensor_operator_eq_zero (ξ : I → H) (η : J → K)
    (hH : ∀ L : H →L[ℂ] E, (∀ i, L (ξ i) = 0) → L = 0)
    (hK : ∀ L : K →L[ℂ] E, (∀ j, L (η j) = 0) → L = 0)
    (T : Completion (H ⊗[ℂ] K) →L[ℂ] E)
    (hT : ∀ i j, T ((ξ i ⊗ₜ[ℂ] η j : H ⊗[ℂ] K) : Completion _) = 0) : T = 0 := by
  let C : H ⊗[ℂ] K →L[ℂ] Completion (H ⊗[ℂ] K) := Completion.toComplL
  have hright (i : I) (y : K) : T (C (ξ i ⊗ₜ[ℂ] y)) = 0 := by
    let L := T.comp (C.comp (TensorProduct.mkL ℂ H K (ξ i)))
    have hz : L = 0 := hK L (hT i)
    exact congrArg (fun F : K →L[ℂ] E => F y) hz
  have hall (x : H) (y : K) : T (C (x ⊗ₜ[ℂ] y)) = 0 := by
    let L := T.comp (C.comp ((TensorProduct.mkL ℂ H K).flip y))
    have hz : L = 0 := hH L (fun i => hright i y)
    exact congrArg (fun F : H →L[ℂ] E => F x) hz
  apply ContinuousLinearMap.ext
  intro z
  change T z = 0
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq T.continuous continuous_const
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [Completion.coe_add, map_add, hx, hy, add_zero]
    | tmul x y => exact hall x y

end WeakPureInfiniteness

end

end OAI
