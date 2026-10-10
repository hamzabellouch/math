import OAI.MeasureTheory.Falconer.Angular.AngularPairCircleIntegral
import OAI.MeasureTheory.Falconer.Angular.AngularFarStationaryScale

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem uniform_actual_far_circle_expansion {sig T : ℝ} (hsig : 0 < sig) (K : ℕ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L ≤ N, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (hsp : Plane → ℂ) (x y : Plane),
    ‖hsp x‖ ≤ 1 → ‖hsp y‖ ≤ 1 →
    ∀ v h L₀ s θ₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    4*(2:ℝ)^(-h) ≤ ‖x-y‖ → 1/4 ≤ s → x-y = ‖x-y‖ • sourceDirection θ₀ →
    let β := inheritedCircleSymbol S b k Q ρ m N lam sig J i hsp
    let f := fun t => β x (sourceUnitDirection t)*conj (β y (sourceUnitDirection t))
    ‖angularPairCircleIntegral β x y ((2:ℝ)^v*s) -
      fullCircleStationaryExpansion ((2:ℝ)^v*s*‖x-y‖) (fun t => f (t+θ₀)) n‖ ≤
      ((2:ℝ)^v*s*‖x-y‖)^(-1/2:ℝ)*((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_actual_two_point_stationary (T := T) (by norm_num : (0:ℝ) < 18) hsig K
  refine ⟨n,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp x y hx hy
    v h L₀ s θ₀ hv hLL₀ hL₀ hd hs hangle
  have hfreq := far_bump_frequency hv hd hs
  have hslack := actual_far_stationary_slack hsig.le N L hLL₀ hL₀ hfreq
  dsimp only
  rw [angularPairCircleIntegral_cosine _
    (fun z => inheritedCircleSymbol_continuous S b k Q hQ ρ m N lam sig J i hsp z)
    x y ((2:ℝ)^v*s) θ₀ hangle]
  exact h₀ N hN S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp x y hx hy
    θ₀ ((2:ℝ)^v*s*‖x-y‖) hslack.1 hslack.2

end PlanarFalconer

end OAI
