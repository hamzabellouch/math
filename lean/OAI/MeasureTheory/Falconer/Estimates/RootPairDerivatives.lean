import OAI.MeasureTheory.Falconer.Shells.RootEndpointData

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_root_pair_derivatives {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ d e : RootEndpointData, 0 < d.Q.side → 0 < e.Q.side →
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    ∀ k l : PolicyDescriptor → ℕ, (∑ b ∈ d.S, k b) ≤ K → (∑ b ∈ e.S, l b) ≤ K →
    ∀ L : ℕ, (∀ b ∈ d.S, descriptorLength b ≤ L) →
    (∀ b ∈ e.S, descriptorLength b ≤ L) →
    ∀ (h g : Plane → ℂ) (x y : Plane), ‖h x‖ ≤ 1 → ‖g y‖ ≤ 1 →
    let f := fun θ => d.symbol N sig k h x (sourceUnitDirection θ) *
      conj (e.symbol N sig l g y (sourceUnitDirection θ))
    ContDiff ℝ ∞ f ∧ ∀ j ≤ n, ∀ θ, ‖iteratedDeriv j f θ‖ ≤ C*sourceSymbolScale N sig L^j := by
  obtain ⟨C,hC,N₀,h₀⟩ := uniform_actual_symbol_derivatives_upto hsig K n
  refine ⟨C*C*2^n,by positivity,N₀,?_⟩
  intro N hN d e hd he hc₁ hc₂ k l hk hl L hL₁ hL₂ h g x y hx hy
  have hf := inheritedCircleSymbol_contDiff d.S id k d.Q hd d.ρ d.mass N d.lam sig d.J d.i h x
  have hg := inheritedCircleSymbol_contDiff e.S id l e.Q he e.ρ e.mass N e.lam sig e.J e.i g y
  refine ⟨hf.mul (Complex.conjCLE.contDiff.comp hg),?_⟩
  exact complex_pair_derivatives_upto hf hg hC hC (sourceSymbolScale_pos N sig L).le n
    (h₀ N hN d.S id k hc₁ hk L hL₁ d.Q hd d.ρ d.mass d.lam d.J d.i h x hx)
    (h₀ N hN e.S id l hc₂ hl L hL₂ e.Q he e.ρ e.mass e.lam e.J e.i g y hy)

end PlanarFalconer

end OAI
