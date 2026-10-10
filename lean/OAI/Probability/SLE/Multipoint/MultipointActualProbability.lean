import OAI.Probability.SLE.Multipoint.MultipointActualBudget
import OAI.Probability.SLE.Multipoint.MultipointActualCutoffs
import OAI.Probability.SLE.Multipoint.MultipointCompletionExhaustion

namespace OAI

/-! The fixed-order radius estimate in an arbitrary conformal image.
The only analytic input not proved here is the stated disk growth bound. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

theorem actual_radius_multipoint_bound
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (J : ℂ → ℂ)
    (hJ : DifferentiableOn ℂ J upperHalfPlane) (hJinj : InjOn J upperHalfPlane)
    (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane) (hne : Function.Injective z)
    (R b e : ι → ℝ) (he : ∀ i, 0 < e i) (heb : ∀ i, e i ≤ b i)
    (hbR : ∀ i, b i ≤ R i) (hRdef : ∀ i, R i = 2*(z i).im*‖deriv J (z i)‖)
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (J (z i)) (J (z j))) :
    P {ω | ∀ i, radiusLevelTime (γ ω) (G ω) (z i) (Real.log (R i/e i)) < ⊤} ≤
      ENNReal.ofReal ((3 : ℝ)^(Fintype.card ι) *
        Real.exp (uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset ι)) *
        ∏ i, (e i/b i)^(1-κ/8)) := by
  classical
  let u₀ := fun i => Real.log (R i/b i)
  let u₂ := fun i => Real.log (R i/e i)
  let a := fun i => sourceClockLevel κ (z i) (u₀ i)
  let U := fun i => κ/4*(u₂ i-u₀ i)
  let A := ‖fun i => Real.log (z i).im‖
  let K := uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset ι)
  have hb (i : ι) : 0 < b i := (he i).trans_le (heb i)
  have hR (i : ι) : 0 < R i := (hb i).trans_le (hbR i)
  have hparams (i : ι) := physical_radius_level_parameters hκ (z i)
    (R i) (b i) (e i) (he i) (heb i) (hbR i)
  have h₀ (i : ι) : 0 ≤ u₀ i := (hparams i).1
  have hu (i : ι) : u₀ i ≤ u₂ i := (hparams i).2.1
  have hU (i : ι) : U i = sourceTarget κ (b i) (e i) := by
    have hh := (hparams i).2.2.2.1
    dsimp [U,u₀,u₂,sourceClockLevel] at *
    linarith
  obtain ⟨_,hβ,hβ1,hdecay,_⟩ := source_parameters hκ hκ8
  obtain ⟨S⟩ := exists_actual_localizations hB hm hBm hBc hB0 hκ hκ8 z hz u₀ u₂ h₀ hu
    γ G F hw A (norm_nonneg _) (initial_log_height_bound z)
  let ρ := fun n : ℕ => actualFactorStops γ G z u₀ u₂ ((n : ℝ≥0)+1)
  have horder (n : ℕ) := (actualFactorStops_regular hB hm hBm hBc hB0 κ hκ hκ8
    γ G F hw z hz u₀ u₂ h₀ hu ((n : ℝ≥0)+1)).2.1
  have hex (n : ℕ) := actual_localized_product_expectation hB hm hBm hBc hB0 hκ hκ8
    hβ.le hβ1 z hz u₀ u₂ h₀ hu γ G F hw (S n)
  choose r C hrm hrp hrb hcost hI hmean using hex
  let E := {ω | ∀ i, radiusLevelTime (γ ω) (G ω) (z i) (u₂ i) < ⊤}
  let cutoff := fun n => {ω | phaseAt (ρ n) ((S n).χ ω) ω = fun _ => 3}
  have hcover : ∀ ω ∈ E, ∀ᶠ n : ℕ in atTop, ω ∈ cutoff n := by
    intro ω hω
    filter_upwards [eventually_all_completed_of_finite_radius_levels B hm hBc κ A
      (norm_nonneg _) z u₀ u₂ γ G F hw S ω hω] with n hn
    exact hn.2
  have hbudget (n : ℕ) (ω : Ω) : discountClock (r n) ((S n).χ ω) ω ≤ K :=
    actual_localized_discount_le hBc hκ hκ8 hβ hdecay z hne u₀ u₂ h₀ hu γ G F hw
      (S n) (horder n) hgrowth J hJ hJinj R b hR hb hRdef (fun _ => rfl) hsep
      (r n) (C n) (hrm n) (fun t ω => (hrb n t ω).2) (hcost n) ω
  have hbound := measure_le_of_completed_phase_products P E cutoff κ (sourceBeta κ) a U K
    (fun n ω => phaseAt (ρ n) ((S n).χ ω) ω)
    (fun n ω => (S n).Q ((S n).χ ω) ω)
    (fun n ω => discountClock (r n) ((S n).χ ω) ω)
    (fun n ω => B ((S n).χ ω) ω)
    hcover hI hmean (fun _ _ h => h) (fun n ω _ => hbudget n ω)
  have hexp := source_radius_targets_exponential (Finset.univ : Finset ι) hκ b e
    (fun i _ => hb i) (fun i _ => he i)
  simpa only [E,u₂,K,show U = (fun i => sourceTarget κ (b i) (e i)) from funext hU,
    hexp] using hbound

end SLEExactGauge.Multipoint

end

end OAI
