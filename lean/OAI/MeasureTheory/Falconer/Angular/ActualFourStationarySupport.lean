import OAI.MeasureTheory.Falconer.Angular.FourStationarySupport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_actual_four_approximant_good {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : Fin 2 → ℝ → ℝ) (q a₀ t₀ a b v : ℕ), 0 < q → a₀ ≤ b → v ≤ t₀ →
    a ≤ b → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun n => m l n-(n:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    ∀ (lam : Fin 2 → ℝ) (i : Fin 2 → ℕ) (h : Fin 2 → Plane → ℂ) (X : Fin 4 → Set Plane),
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l) N (lam l) sig J (i l) (h l)
    ∀ᵐ x ∂Measure.pi (fun j => (![ρ 0,ρ 0,ρ 1,ρ 1] j).restrict (X j)),
    ∀ (n : ℕ) (w : ℝ) (Ψ : ℝ → ℝ), (∀ t, Ψ t ≠ 0 → 0 < t) →
    x 0 ≠ x 1 → x 2 ≠ x 3 → angularStationarySpatialKernel (β 0) (β 1) n w Ψ x ≠ 0 →
    (x 0,x 1) ∈ positiveDistanceGoodSet (Q 0) (ρ 0) (m 0) N q b v (lam 0) sig J (i 0+1) ∧
    (x 2,x 3) ∈ positiveDistanceGoodSet (Q 1) (ρ 1) (m 1) N q b v (lam 1) sig J (i 1+1) := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_pair_approximant_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a b v hq hl hr hab hv S k hS lam i h X
  have hp (l : Fin 2) := h₀ N hN (Q l) (hQ l) (ρ l) (hcarry l) (m l)
    q a₀ t₀ a b v hq hl hr hab hv (S l) (k l) (hS l) (lam l) (i l) (h l)
  have hh := pair_ae_four_restrictions (ρ 0) (ρ 1) X _ _ (hp 0) (hp 1)
  filter_upwards [hh] with x hx
  intro n w Ψ hs hx₁ hx₂ hn
  exact stationary_spatial_good_of_pair_good _ _ _ _ x hx.1 hx.2 hs n w hx₁ hx₂ hn

end PlanarFalconer

end OAI
