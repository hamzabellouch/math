import OAI.Probability.SLE.Stochastic.BrownianStateAE
import OAI.Probability.SLE.Multipoint.MultipointCompactField
import OAI.Probability.SLE.Multipoint.MultipointPiecewiseClock
import OAI.Probability.SLE.Multipoint.MultipointDiscountCost

namespace OAI

/-! The compact discounted product along adapted Loewner states. The
discount rate may jump at stopping times. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge.Multipoint

theorem exists_bounded_discount_cost_process
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (Q : ℝ → Ω → (ι → ℂ × ℝ))
    (hQm : Measurable (fun p : ℝ × Ω => Q p.1 p.2))
    (hQa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => Q t))
    (hQc : ∀ ω, Continuous (fun t => Q t ω))
    (s : Finset ι) (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (g : ℝ≥0 → Ω → ℝ) (C : ℝ≥0),
      Measurable (Function.uncurry g) ∧
      IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) g ∧
      (∀ ω, Continuous (fun t => g t ω)) ∧
      (∀ t ω, 0 ≤ g t ω ∧ |g t ω| ≤ C) ∧
      (∀ (t : ℝ≥0) ω, ‖(Q t ω,B t ω)‖ ≤ R →
        g t ω = productDriftCost s κ D σ (Q t ω) (B t ω)) := by
  obtain ⟨G, C, hG, hGb, hGe⟩ := exists_bounded_discount_cost s κ hκ hκ8 D σ hD R hR
  let g := fun (t : ℝ≥0) ω => G (Q t ω,B t ω)
  have hQn : Measurable (fun p : ℝ≥0 × Ω => Q p.1 p.2) :=
    hQm.comp ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hga : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) g :=
    fun t => hG.measurable.comp ((hQa t).prodMk ((Filtration.stronglyAdapted_natural
      (fun t => (hm t).stronglyMeasurable)).adapted t))
  have hgc (ω : Ω) : Continuous (fun t => g t ω) :=
    hG.comp (((hQc ω).comp NNReal.continuous_coe).prodMk (hBc ω))
  refine ⟨g, C, hG.measurable.comp (hQn.prodMk hBm), ?_, hgc, ?_, ?_⟩
  · have hs : StronglyAdapted (Filtration.natural B
        (fun t => (hm t).stronglyMeasurable)) g := fun t => (hga t).stronglyMeasurable
    exact (hs.isStronglyProgressive_of_continuous hgc).isProgressive
  · exact fun t ω => hGb (Q t ω,B t ω)
  · exact fun t ω ht => hGe (Q t ω,B t ω) ht

theorem compact_discounted_smooth_field
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (Q V : ℝ → Ω → (ι → ℂ × ℝ)) (L : ℝ≥0)
    (hQm : Measurable (fun p : ℝ × Ω => Q p.1 p.2))
    (hQa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => Q t))
    (hQl : ∀ ω, LipschitzWith L (fun t => Q t ω))
    (hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2))
    (hVb : ∀ t ω, ‖V t ω‖ ≤ L)
    (hQd : ∀ ω, ∀ᵐ t : ℝ, 0 < t → HasDerivAt (fun u => Q u ω) (V t ω) t)
    (r : ℝ≥0 → Ω → ℝ) (hrm : Measurable (Function.uncurry r))
    (hrp : IsProgressive (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) r)
    (C : ℝ≥0) (hrb : ∀ t ω, |r t ω| ≤ C)
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ (φ : ((ι → ℂ × ℝ) × ℝ) × ℝ → ℝ) (K : ℝ≥0),
      (∀ p, 0 ≤ φ p) ∧
      (∀ z x, ‖(z,x)‖ ≤ R → φ (z,x) = discountedProduct s κ D σ z x) ∧
      (∀ z x, ‖(z,x)‖ ≤ R → fderiv ℝ φ (z,x) =
        fderiv ℝ (fun p => discountedProduct s κ D σ p.1 p.2) (z,x)) ∧
      (∀ z x, ‖(z,x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (z,y)) x =
        iteratedDeriv 2 (discountedProduct s κ D σ z) x) ∧
      SmoothTimeBrownianField B hm K
        (fun t ω x => φ ((Q t ω, discountClock r t ω),x))
        (fun t ω x => fderiv ℝ φ ((Q t ω, discountClock r t ω),x)
          ((V t ω, r t ω),0)) := by
  obtain ⟨φ, hφ, hφc, hφ0, he, heD, he2⟩ :=
    exists_compact_discounted_field s κ D σ hD R hR
  have hrt (ω : Ω) : Measurable (fun t => r t ω) :=
    hrm.comp (measurable_id.prodMk measurable_const)
  have hcm := discountClock_measurable r hrm
  have hca := discountClock_adapted_of_progressive _ r hrp
  have hcl := discountClock_lipschitz_of_measurable r hrt C hrb
  have hcd := discountClock_ae_derivative r hrt C hrb
  let Q' := fun t ω => (Q t ω, discountClock r t ω)
  let V' := fun t ω => (V t ω, r t.toNNReal ω)
  have hQ'm : Measurable (fun p : ℝ × Ω => Q' p.1 p.2) := hQm.prodMk hcm
  have hQ'a : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => Q' t) := fun t => (hQa t).prodMk (hca t)
  have hQ'l (ω : Ω) : LipschitzWith (max L C) (fun t => Q' t ω) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    rw [Prod.dist_eq]
    exact max_le
      (((hQl ω).dist_le_mul t u).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left L C) dist_nonneg))
      (((hcl ω).dist_le_mul t u).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right L C) dist_nonneg))
  have hrm' : Measurable (fun p : ℝ × Ω => r p.1.toNNReal p.2) :=
    hrm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hV'm : Measurable (fun p : ℝ × Ω => V' p.1 p.2) := hVm.prodMk hrm'
  have hV'b (t : ℝ) (ω : Ω) : ‖V' t ω‖ ≤ (max L C : ℝ≥0) := by
    rw [Prod.norm_def]
    have hrnorm : ‖r t.toNNReal ω‖ ≤ (C : ℝ) := by
      simpa only [Real.norm_eq_abs] using hrb t.toNNReal ω
    exact max_le
      ((hVb t ω).trans (by exact_mod_cast le_max_left L C))
      (hrnorm.trans (by exact_mod_cast le_max_right L C))
  have hQ'd (ω : Ω) : ∀ᵐ t : ℝ, 0 < t →
      HasDerivAt (fun u => Q' u ω) (V' t ω) t := by
    filter_upwards [hQd ω, hcd ω] with t hq hc
    intro ht
    exact (hq ht).prodMk (hc ht)
  obtain ⟨K, hK⟩ := compact_state_smooth_brownian_field_of_ae_deriv B hm Q' V'
    (max L C) hQ'm hQ'a hQ'l hV'm hV'b hQ'd φ hφ hφc
  refine ⟨φ, K, hφ0, he, heD, he2, ?_⟩
  simpa only [Q', V', Real.toNNReal_coe] using hK

lemma compact_discounted_process_drift_nonpos
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℝ≥0 → Ω → ℝ) (Q V : ℝ → Ω → (ι → ℂ × ℝ))
    (r : ℝ≥0 → Ω → ℝ) (s : Finset ι)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (D σ : ι → ℝ)
    (φ : ((ι → ℂ × ℝ) × ℝ) × ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (ω : Ω)
    (hD : ∀ i ∈ s, 0 < D i) (hσ : ∀ i ∈ s, σ i ≤ 1)
    (hδ : ∀ i ∈ s, branchRegulator κ (D i) (σ i) (Q t ω i) ≤ 1)
    (hV : ∀ i ∈ s, V t ω i = physicalLogLoewnerField
      (Real.sqrt κ*B t.toNNReal ω) (Q t ω i))
    (hr : r t.toNNReal ω = productDriftCost s κ D σ (Q t ω) (B t.toNNReal ω))
    (hφD : fderiv ℝ φ ((Q t ω,discountClock r t ω),B t.toNNReal ω) =
      fderiv ℝ (fun p => discountedProduct s κ D σ p.1 p.2)
        ((Q t ω,discountClock r t ω),B t.toNNReal ω))
    (hφ2 : iteratedDeriv 2 (fun y => φ ((Q t ω,discountClock r t ω),y))
      (B t.toNNReal ω) =
      iteratedDeriv 2 (discountedProduct s κ D σ (Q t ω,discountClock r t ω))
        (B t.toNNReal ω)) :
    brownianFieldDrift B
      (fun t ω x => φ ((Q t ω,discountClock r t ω),x))
      (fun t ω x => fderiv ℝ φ ((Q t ω,discountClock r t ω),x)
        ((V t ω,r t ω),0)) t ω ≤ 0 := by
  unfold brownianFieldDrift
  simp only [Real.coe_toNNReal t ht]
  rw [hr, hφD, hφ2, discountedProduct_pair_directional,
    discountedProduct_directional_congr s κ D σ hD (Q t ω) _ _
      (discountClock r t ω) (productDriftCost s κ D σ (Q t ω) (B t.toNNReal ω))
      (B t.toNNReal ω) hV]
  exact discountedProduct_generator_nonpos s κ hκ hκ8 D σ (Q t ω)
    (discountClock r t ω) (B t.toNNReal ω) hD hσ hδ

end SLEExactGauge.Multipoint

end

end OAI
