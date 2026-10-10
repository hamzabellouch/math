import OAI.MeasureTheory.Falconer.Estimates.ActualNoncomparableMain
import OAI.MeasureTheory.Falconer.Radial.ActualSingleRadialError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_actual_noncomparable_radial {sig T : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → ∀ x y : Fin 2 → Plane,
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v h L₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    (4*(2:ℝ)^(-h) ≤ ‖x 0-y 0‖) → 2*‖x 1-y 1‖ ≤ ‖x 0-y 0‖ →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    ‖angularOriginalSpatialKernel (β 0) (β 1) v Ψ ![x 0,y 0,x 1,y 1]‖ ≤
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₁,h₁⟩ := uniform_actual_single_radial_error (T := T+1) hsig K
    hΨ.continuous.measurable hpos hs hW hw
  obtain ⟨N₂,h₂⟩ := uniform_actual_noncomparable_main (T := T+1) hΨ hs hsig K n
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp hm x y hx hy
    v h L₀ hv hLL hL₀ hd hsep
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N (lam l) sig (J l) (i l) (hsp l)
  let z : Fin 4 → Plane := ![x 0,y 0,x 1,y 1]
  have he := h₁ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) S b k hcard hK
    L hLN hL Q hQ ρ m lam J i hsp hm x y hx hy v h L₀ hv hLL hL₀ hd
    (fun l => angularPairAngle (x l) (y l)) (fun l => angularPairAngle_represents _ _)
  have hmterm := h₂ N ((le_max_right _ _).trans ((le_max_right _ _).trans hN)) S b k hcard hK
    L hL Q hQ ρ m lam J i hsp x y hx hy v h L₀ hv hLL hL₀ hd hsep
  change ‖angularOriginalSpatialKernel (β 0) (β 1) v Ψ z -
    angularSingleStationaryKernel (β 0) (β 1) n v Ψ z‖ ≤ ((2:ℝ)^N)^(-(T+1)) at he
  have ht := norm_add_le
    (angularOriginalSpatialKernel (β 0) (β 1) v Ψ z-angularSingleStationaryKernel (β 0) (β 1) n v Ψ z)
    (angularSingleStationaryKernel (β 0) (β 1) n v Ψ z)
  rw [sub_add_cancel] at ht
  apply (ht.trans (add_le_add he hmterm)).trans
  have hR : (2:ℝ) ≤ (2:ℝ)^N := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) ((le_max_left _ _).trans hN)
  have hRp : 0 < (2:ℝ)^N := by positivity
  calc
    _ = 2*((2:ℝ)^N)^(-(T+1)) := by ring
    _ ≤ (2:ℝ)^N*((2:ℝ)^N)^(-(T+1)) := mul_le_mul_of_nonneg_right hR (by positivity)
    _ = _ := by
      nth_rw 1 [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add hRp]
      congr 1
      ring

end PlanarFalconer

end OAI
