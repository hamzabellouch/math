import OAI.Analysis.CircleDomains.Rigidity.MaskedWedgeCost

namespace OAI

/-!
# Common grid selection from masked L² fields

The correction terms are integrated only where both coordinates are
present. Their finite sum is independent of width. Shrinking the grid
spacing therefore permits the same terminal-count and good-width
selection used for globally defined coordinates.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_grid_for_masked_wedge_cost
    {X P S : Type*} [MeasurableSpace X] [Fintype P] [Countable S]
    {μ : Measure X} [SFinite μ] {n : ℕ}
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (M : Fin n → Set X) (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ)
    (hu : ∀ i, Measurable (u i)) (hc : Measurable c)
    (hx : ∀ i, Measurable (x i)) (hχ : Measurable χ)
    (hu2 : ∀ i, MemLp (u i) 2 (μ.restrict (M i))) (hc2 : MemLp c 2 μ)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (Q : ℕ → (Fin n → ℝ) → Prop)
    (hQ : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, Q N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hsmall : (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
      |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂μ) < η / 4) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < ρ ∧ Q N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).ncard : ℝ) < η ∧
      ∃ᶠ k in atTop, maskedStaircaseCost μ pairs M u c x χ (reciprocalGridStep N)
        (staircaseWidth (reciprocalGridStep N) k) θ < η := by
  let W : ℕ → ℕ → (Fin n → ℝ) → ℝ := fun N k =>
    maskedStaircaseCost μ pairs M u c x χ (reciprocalGridStep N)
      (staircaseWidth (reciprocalGridStep N) k)
  have hestimate N k := integrable_maskedStaircaseCost_and_mean_le pairs hpairs
    M u c x χ hu hc hx hχ hu2 hc2 (reciprocalGridStep_pos N)
    (staircaseWidth_pos (reciprocalGridStep_pos N) k)
    (staircaseWidth_lt (reciprocalGridStep_pos N) k) hχ0 hχ1
  have hlimit := ((reciprocalGridStep_tendsto_zero.mul_const
    (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
      |planarWedge (u (pairs p).1 z) (c z)| +
        |planarWedge (c z) (u (pairs p).2 z)| ∂μ)).const_add
      (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
        |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂μ))
  simp only [zero_mul, add_zero] at hlimit
  have hmean : ∀ᶠ N in atTop, ∀ k, (∫ θ, W N k θ ∂reciprocalGridLaw n N) < η / 4 := by
    filter_upwards [hlimit.eventually_lt_const hsmall] with N hN k
    exact (hestimate N k).2.trans_lt hN
  exact exists_grid_with_finite_terminals_and_good_widths F hF pairs hpairs a b
    hwidth hwidth2 W Q hη hρ (fun N k => (hestimate N k).1)
    (fun N k => Filter.Eventually.of_forall
      (maskedStaircaseCost_nonneg μ pairs M u c x χ _ _)) hQ hmean

end CircleDomainRigidity.FiniteTransfer

end

end OAI
