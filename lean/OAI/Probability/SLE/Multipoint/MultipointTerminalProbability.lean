import OAI.Probability.SLE.Multipoint.MultipointPhaseProcess

namespace OAI

/-! Convert the real-valued stopped product estimate into the successful
event probability, after exhaustion by the concrete localizations. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal

namespace SLEExactGauge.Multipoint

lemma initial_phase_product_le_one
    {Ω ι : Type*} [Fintype ι]
    (κ β : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (a U : ι → ℝ) (hU : ∀ i, 0 ≤ U i)
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (ω : Ω)
    (horder : ∀ i, Monotone (fun k => ρ (i,k) ω))
    (z : ι → ℂ × ℝ) (x : ℝ)
    (hclock : ∀ i (k : Fin 3), ρ (i,k) ω = 0 →
      logFactorClock κ (z i)-a i = if k = 0 then 0 else if k = 1 then U i/2 else U i) :
    patternProduct κ β a U (phaseAt ρ 0 ω) z x ≤ 1 := by
  rw [← patternProduct_all_inactive κ β a U z x]
  apply patternProduct_switch_le κ β hκ hκ8 a U hU _ _ _ _ (fun _ => bot_le)
  · intro i _ hi
    have hh := (phaseAt_ge_iff ρ ω i (horder i) 0 0).mp hi
    simpa only [ite_true] using hclock i 0 (le_antisymm hh bot_le)
  · intro i _ hi
    have hh := (phaseAt_ge_iff ρ ω i (horder i) 0 1).mp hi
    simpa only [Fin.reduceEq, ite_true, ite_false] using hclock i 1 (le_antisymm hh bot_le)
  · intro i _ hi
    have hh := (phaseAt_ge_iff ρ ω i (horder i) 0 2).mp hi
    simpa only [Fin.reduceEq, ite_true, ite_false] using hclock i 2 (le_antisymm hh bot_le)

lemma measure_le_of_eventual_real_products
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (cutoff : ℕ → Set Ω) (X : ℕ → Ω → ℝ) (q : ℝ) (hq : 0 < q)
    (hcover : ∀ ω ∈ E, ∀ᶠ n : ℕ in atTop, ω ∈ cutoff n)
    (hX : ∀ n, Integrable (X n) P) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (hmean : ∀ n, (∫ ω, X n ω ∂P) ≤ 1)
    (hterminal : ∀ n ω, ω ∈ cutoff n → q ≤ X n ω) :
    P E ≤ ENNReal.ofReal q⁻¹ := by
  apply measure_le_of_eventual_stopped_products P E cutoff (fun n ω => ENNReal.ofReal (X n ω)) q hq hcover
  · intro n
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hX n).aestronglyMeasurable.aemeasurable
  · intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hX n) (ae_of_all _ (hX0 n))]
    exact (ENNReal.ofReal_le_ofReal (hmean n)).trans_eq ENNReal.ofReal_one
  · exact fun n ω hω => ENNReal.ofReal_le_ofReal (hterminal n ω hω)

theorem measure_le_of_completed_phase_products
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (E : Set Ω) (cutoff : ℕ → Set Ω)
    (κ β : ℝ) (a U : ι → ℝ) (K : ℝ)
    (j : ℕ → Ω → ι → Fin 4) (Q : ℕ → Ω → ι → ℂ × ℝ)
    (b x : ℕ → Ω → ℝ)
    (hcover : ∀ ω ∈ E, ∀ᶠ n : ℕ in atTop, ω ∈ cutoff n)
    (hI : ∀ n, Integrable (fun ω => discountedPatternProduct κ β a U (j n ω)
      (Q n ω,b n ω) (x n ω)) P)
    (hmean : ∀ n, (∫ ω, discountedPatternProduct κ β a U (j n ω)
      (Q n ω,b n ω) (x n ω) ∂P) ≤ 1)
    (hcomplete : ∀ n ω, ω ∈ cutoff n → j n ω = fun _ => 3)
    (hb : ∀ n ω, ω ∈ cutoff n → b n ω ≤ K) :
    P E ≤ ENNReal.ofReal ((3 : ℝ)^(Fintype.card ι)*Real.exp K*
      Real.exp (-greenExponent κ/2 * ∑ i, U i)) := by
  have hbound := measure_le_of_eventual_real_products P E cutoff
    (fun n ω => discountedPatternProduct κ β a U (j n ω) (Q n ω,b n ω) (x n ω))
    (successBarrier (greenExponent κ) K Finset.univ U)
    (successBarrier_pos _ _ _ _) hcover hI
    (fun n ω => mul_nonneg (Real.exp_pos _).le
      (Finset.prod_nonneg (fun i _ => (phaseFactor_pos κ β (a i) (U i) (j n ω i) (Q n ω i) (x n ω)).le)))
    hmean (fun n ω hω => by
      rw [hcomplete n ω hω]
      exact discountedPatternProduct_complete_lower κ β a U (Q n ω) (b n ω) K (x n ω) (hb n ω hω))
  simpa only [successBarrier_inv, Finset.card_univ] using hbound

end SLEExactGauge.Multipoint

end

end OAI
