import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongCounting
import OAI.NumberTheory.CubicMoment.Estimates.StructuredCoefficientEnergy

namespace OAI

/-! The actual long inverse-completion counting estimate for an
arbitrary logarithmic weight family, with all outer coefficients kept. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.metaplectic_long_counting
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {ε s : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1/2) (hs : 0 < s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein)
      (α : Eisenstein → ℂ) (ℓ : ℤ) (X U B C F : ℝ),
      1 ≤ X → 0 < U → 0 ≤ B → 0 < C → B*U ≤ F →
      (∀ r ∈ A, primary r) → (∀ r ∈ A, Y (w r) ≤ X) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ‖∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W (w r)) U C F‖ ≤
        K*B*U*X^s*(C/2)^(-3/2+ε)*((metaplecticLongDyads C F).card:ℝ)*
          (∑ r ∈ A, ‖α r‖) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_long_outer_counting hε hεsmall
  obtain ⟨M,hM,hMbound⟩ := hW.subpower_norm hs
  refine ⟨D*M,by positivity,?_⟩
  intro w A α ℓ X U B C F hX hU hB hC hF hA hY hcut
  have hb : ∀ r ∈ A, ∀ x, ‖W (w r) x‖ ≤ M*X^s := by
    intro r hr x
    exact (hMbound (w r) x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [hW.length_one (w r)]) (hY r hr) hs.le) hM)
  have hh := hbound A α ℓ (fun r => W (w r)) U B C F (M*X^s)
    hU hB hC hF (by positivity) hA hcut hb
  convert hh using 1
  ring

end CubicFirstMoment

end

end OAI
