import OAI.MeasureTheory.Falconer.Estimates.FarComparableSplit

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_far_stationary_reduction {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (m l)) →
    ∀ (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ a ≤ N, ∀ A : Fin 2 → CellPath, (∀ l, (A l).length = a) →
    ∀ d : ℕ, ∀ v L₀ : ℝ, v ≤ N → v-(a+d:ℕ) = 2*L₀ →
    (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N lam sig (J l) (i l) (hsp l)
    let M := fun l => ((2:ℝ)^N)^(-m l a)
    ‖angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) d a v Ψ
        (M 0) (M 1) (((2:ℝ)^N)^(-m 0 (a+d))) (((2:ℝ)^N)^(-m 1 (a+d))) (β 0) (β 1)
        (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col) -
      angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) a d v (M 0) (M 1)
        (angularStationarySpatialKernel (β 0) (β 1) n v Ψ)‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₁,h₁⟩ := uniform_actual_noncomparable_far (T := T+1) (lam := lam) hsig K hΨ hpos hs hW hw
  obtain ⟨n,N₂,h₂⟩ := uniform_actual_comparable_far_error (T := T+1) (lam := lam) hsig K
    hΨ.continuous.measurable hpos hs hW hw
  refine ⟨n,max 1 (max N₁ N₂),?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m B δ hd J i hsp hm hb a ha A hA
    d v L₀ hvN hv hLL hL₀
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N lam sig (J l) (i l) (hsp l)
  let M := fun l => ((2:ℝ)^N)^(-m l a)
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  have hβ (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ (hm l)
  have hbd (l : Fin 2) (x : Plane) := inheritedCircleSymbol_norm_le
    (S l) (b l) (k l) (Q l) (hQp l) (ρ l) (m l) N lam sig (J l) (i l) (hsp l) K (hK l) x (hb l x)
  have hD : 0 ≤ symbolDerivativeConstant K^K := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have he₁ := h₁ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) S b k hcard hK
    L hLN hL Q hQ ρ m B δ hd J i hsp hm hb a ha A hA d v L₀ hvN hv hLL hL₀
  have he₂ := h₂ N ((le_max_right _ _).trans ((le_max_right _ _).trans hN)) S b k hcard hK
    L hLN hL Q hQ ρ m B δ hd J i hsp hm hb a ha A hA d v L₀ hvN hv hLL hL₀
  dsimp only
  rw [angular_far_comparable_split (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) a d v
    hΨ.continuous.measurable hpos hs hW hw (M 0) (M 1) (by positivity) (by positivity)
    (β 0) (β 1) (hβ 0) (hβ 1) hD hD (hbd 0) (hbd 1),add_sub_assoc]
  apply ((norm_add_le _ _).trans (add_le_add he₁ he₂)).trans
  have hR : (2:ℝ) ≤ (2:ℝ)^N := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) ((le_max_left _ _).trans hN)
  calc
    _ = 2*((2:ℝ)^N)^(-(T+1)) := by ring
    _ ≤ (2:ℝ)^N*((2:ℝ)^N)^(-(T+1)) := mul_le_mul_of_nonneg_right hR (by positivity)
    _ = _ := by
      nth_rw 1 [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring

end PlanarFalconer

end OAI
