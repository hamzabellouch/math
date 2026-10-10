import OAI.MeasureTheory.Falconer.Angular.FullCircleStationaryPower
import OAI.MeasureTheory.Falconer.Angular.RotatedCircleIntegral
import OAI.MeasureTheory.Falconer.Angular.ActualStationaryExpansion

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem inheritedCircleSymbol_periodic {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) :
    Function.Periodic (fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x
      (sourceUnitDirection φ)) (2*Real.pi) := by
  have hp := (inheritedMaskProduct_periodic S b k Q ρ m N lam sig J i (fun _ => x)).nat_mul 2
  intro θ
  simp only [inheritedCircleSymbol_comp]
  rw [show inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x) (θ+2*Real.pi) =
      inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x) θ from by simpa using hp θ]

 theorem uniform_actual_full_circle_stationary {c sig T : ℝ} (hc : 0 < c) (hsig : 0 < sig) (K : ℕ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L ≤ N, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane), ‖h x‖ ≤ 1 →
    ∀ θ₀ Λ : ℝ, ((2:ℝ)^N)^(c*sig) ≤ Λ →
    sourceSymbolScale N sig L^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    let f := fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection φ)
    ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ (θ-θ₀)*f θ) -
      fullCircleStationaryExpansion Λ (fun θ => f (θ+θ₀)) n‖ ≤
      Λ^(-1/2:ℝ)*((2:ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := full_circle_stationary_power (T := T) hc hsig
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_actual_symbol_derivatives_upto hsig K (2*(n+1)+2)
  obtain ⟨N₂,h₂⟩ := hn C hC
  refine ⟨n,max N₁ N₂,?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m lam J i h x hx θ₀ Λ hlower hratio
  let f : ℝ → ℂ := fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection φ)
  have hf : ContDiff ℝ ∞ f := inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h x
  have hp : Function.Periodic f (2*Real.pi) := inheritedCircleSymbol_periodic S b k Q ρ m N lam sig J i h x
  have hfs : ContDiff ℝ ∞ (fun θ => f (θ+θ₀)) := hf.comp (contDiff_id.add contDiff_const)
  have hps : Function.Periodic (fun θ => f (θ+θ₀)) (2*Real.pi) := by
    intro θ
    change f (θ+2*Real.pi+θ₀) = f (θ+θ₀)
    rw [show θ+2*Real.pi+θ₀ = (θ+θ₀)+2*Real.pi by ring,hp]
  have hb : ∀ j ≤ 2*(n+1)+2, ∀ θ, ‖iteratedDeriv j (fun θ => f (θ+θ₀)) θ‖ ≤
      C*sourceSymbolScale N sig L^j := by
    intro j hj θ
    rw [iteratedDeriv_comp_add_const]
    exact h₁ N ((le_max_left _ _).trans hN) S b k hcard hK L hL Q hQ ρ m lam J i h x hx j hj _
  change ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ (θ-θ₀)*f θ) - _‖ ≤ _
  rw [rotated_circle_integral Λ θ₀ hp]
  exact h₂ N ((le_max_right _ _).trans hN) hfs hps (sourceSymbolScale_one_le N hsig.le L)
    hlower (sourceSymbolScale_upper N hsig.le hLN) hratio hb

end PlanarFalconer

end OAI
