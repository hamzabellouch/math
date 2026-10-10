import OAI.MeasureTheory.Falconer.Angular.ActualTwoPointStationary

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem uniform_actual_pair_derivatives {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x y : Plane),
    ‖h x‖ ≤ 1 → ‖h y‖ ≤ 1 →
    let f := fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection φ) *
      conj (inheritedCircleSymbol S b k Q ρ m N lam sig J i h y (sourceUnitDirection φ))
    ContDiff ℝ ∞ f ∧ ∀ j ≤ n, ∀ θ, ‖iteratedDeriv j f θ‖ ≤ C*sourceSymbolScale N sig L^j := by
  obtain ⟨C,hC,N₀,h₀⟩ := uniform_actual_symbol_derivatives_upto hsig K n
  refine ⟨C*C*2^n,by positivity,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i h x y hx hy
  have hfx := inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h x
  have hfy := inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h y
  refine ⟨hfx.mul (Complex.conjCLE.contDiff.comp hfy),?_⟩
  exact complex_pair_derivatives_upto hfx hfy hC hC (sourceSymbolScale_pos N sig L).le n
    (h₀ N hN S b k hcard hK L hL Q hQ ρ m lam J i h x hx)
    (h₀ N hN S b k hcard hK L hL Q hQ ρ m lam J i h y hy)

end PlanarFalconer

end OAI
