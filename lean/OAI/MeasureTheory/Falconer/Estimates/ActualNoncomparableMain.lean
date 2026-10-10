import OAI.MeasureTheory.Falconer.Angular.ActualSingleStationaryKernel
import OAI.MeasureTheory.Falconer.Estimates.NoncomparablePower

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_actual_noncomparable_main {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig T : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ) (x y : Fin 2 → Plane),
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v h L₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    4*(2:ℝ)^(-h) ≤ ‖x 0-y 0‖ → 2*‖x 1-y 1‖ ≤ ‖x 0-y 0‖ →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    ‖angularSingleStationaryKernel (β 0) (β 1) n v Ψ ![x 0,y 0,x 1,y 1]‖ ≤
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨q,hq⟩ := noncomparable_power_absorption (by positivity : 0 < 20*sig) T
  obtain ⟨H,hH,N₁,h₁⟩ := uniform_actual_single_stationary_kernel hΨ hs hsig K n q
  obtain ⟨N₂,h₂⟩ := hq H hH
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i hsp x y hx hy
    v h L₀ hv hLL hL₀ hd hsep
  have hpos : 0 < ‖x 0-y 0‖ := (by positivity : 0 < 4*(2:ℝ)^(-h)).trans_le hd
  have hD := sourceSymbolScale_far_frequency_le hsig.le N L hv hLL hL₀ hd
  have he := h₁ N ((le_max_left _ _).trans hN) S b k hcard hK L hL Q hQ
    ρ m lam J i hsp x y hx hy v hpos hsep hD
  apply he.trans
  apply h₂ N ((le_max_right _ _).trans hN)
  have hf : (2:ℝ)^(2*L₀) ≤ (2:ℝ)^v*‖x 0-y 0‖ := by
    simpa only [mul_one] using far_bump_frequency hv hd (by norm_num : (1/4:ℝ) ≤ 1)
  apply le_trans _ hf
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

end PlanarFalconer

end OAI
