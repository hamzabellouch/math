import OAI.Probability.SLE.Multipoint.MultipointDiscountProcess
import OAI.Probability.SLE.Stochastic.BrownianOptionalIntervals

namespace OAI

/-! The actual discounted regularized product has nonincreasing conditional
expectation on each localized interval of constant active pattern. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge.Multipoint

theorem discounted_product_optional_interval_le
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (Q V : ℝ → Ω → (ι → ℂ × ℝ)) (r : ℝ≥0 → Ω → ℝ)
    (s : Finset ι) (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i) (hσ : ∀ i ∈ s, σ i ≤ 1)
    (φ : ((ι → ℂ × ℝ) × ℝ) × ℝ → ℝ) (K : ℝ≥0)
    (hF : SmoothTimeBrownianField B hm K
      (fun t ω x => φ ((Q t ω,discountClock r t ω),x))
      (fun t ω x => fderiv ℝ φ ((Q t ω,discountClock r t ω),x)
        ((V t ω,r t ω),0)))
    (R : ℝ)
    (he : ∀ z x, ‖(z,x)‖ ≤ R → φ (z,x) = discountedProduct s κ D σ z x)
    (heD : ∀ z x, ‖(z,x)‖ ≤ R → fderiv ℝ φ (z,x) =
      fderiv ℝ (fun p => discountedProduct s κ D σ p.1 p.2) (z,x))
    (he2 : ∀ z x, ‖(z,x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (z,y)) x =
      iteratedDeriv 2 (discountedProduct s κ D σ z) x)
    (a b : Ω → ℝ≥0)
    (ha : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (a ω : WithTop ℝ≥0)))
    (hb : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (b ω : WithTop ℝ≥0)))
    (hab : ∀ ω, a ω ≤ b ω) (T : ℝ≥0) (hbT : ∀ ω, b ω ≤ T)
    {A : Set Ω} (hA : MeasurableSet[ha.measurableSpace] A)
    (hnorm : ∀ ω ∈ A, ∀ u, (a ω : ℝ) ≤ u → u ≤ (b ω : ℝ) →
      ‖((Q u ω,discountClock r u ω),B u.toNNReal ω)‖ ≤ R)
    (hδ : ∀ ω ∈ A, ∀ u, (a ω : ℝ) ≤ u → u < (b ω : ℝ) →
      ∀ i ∈ s, branchRegulator κ (D i) (σ i) (Q u ω i) ≤ 1)
    (hV : ∀ ω ∈ A, ∀ u, (a ω : ℝ) ≤ u → u < (b ω : ℝ) →
      ∀ i ∈ s, V u ω i = physicalLogLoewnerField
        (Real.sqrt κ*B u.toNNReal ω) (Q u ω i))
    (hr : ∀ ω ∈ A, ∀ u, (a ω : ℝ) ≤ u → u < (b ω : ℝ) →
      r u.toNNReal ω = productDriftCost s κ D σ (Q u ω) (B u.toNNReal ω)) :
    IntegrableOn (fun ω => discountedProduct s κ D σ
      (Q (b ω) ω,discountClock r (b ω) ω) (B (b ω) ω)) A P ∧
    IntegrableOn (fun ω => discountedProduct s κ D σ
      (Q (a ω) ω,discountClock r (a ω) ω) (B (a ω) ω)) A P ∧
    (∫ ω in A, discountedProduct s κ D σ
      (Q (b ω) ω,discountClock r (b ω) ω) (B (b ω) ω) ∂P) ≤
      ∫ ω in A, discountedProduct s κ D σ
        (Q (a ω) ω,discountClock r (a ω) ω) (B (a ω) ω) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hAm : MeasurableSet A := ha.measurableSpace_le _ hA
  have habe (ω : Ω) : (a ω : ℝ) ≤ (b ω : ℝ) := by exact_mod_cast hab ω
  have hea : (fun ω => φ ((Q (a ω) ω,discountClock r (a ω) ω),B (a ω) ω))
      =ᵐ[P.restrict A] (fun ω => discountedProduct s κ D σ
        (Q (a ω) ω,discountClock r (a ω) ω) (B (a ω) ω)) := by
    filter_upwards [ae_restrict_mem hAm] with ω hω
    apply he
    simpa only [Real.toNNReal_coe] using hnorm ω hω (a ω) le_rfl (habe ω)
  have heb : (fun ω => φ ((Q (b ω) ω,discountClock r (b ω) ω),B (b ω) ω))
      =ᵐ[P.restrict A] (fun ω => discountedProduct s κ D σ
        (Q (b ω) ω,discountClock r (b ω) ω) (B (b ω) ω)) := by
    filter_upwards [ae_restrict_mem hAm] with ω hω
    apply he
    simpa only [Real.toNNReal_coe] using hnorm ω hω (b ω) (habe ω) le_rfl
  have hIb := hF.eval_stopped_integrable (P := P.restrict A) hBm
    (stopping_time_measurable_nnreal hb)
  have hIa := hF.eval_stopped_integrable (P := P.restrict A) hBm
    (stopping_time_measurable_nnreal ha)
  refine ⟨hIb.congr heb, hIa.congr hea, ?_⟩
  rw [← integral_congr_ae heb, ← integral_congr_ae hea]
  apply brownian_time_field_optional_interval_le hB hm hBm hBc hF a b ha hb hab T hbT hA
  intro ω hω u hau hub
  exact compact_discounted_process_drift_nonpos B Q V r s κ hκ hκ8 D σ φ u
    (le_trans (a ω).coe_nonneg hau) ω hD hσ (hδ ω hω u hau hub)
    (hV ω hω u hau hub) (hr ω hω u hau hub)
    (heD _ _ (hnorm ω hω u hau hub.le)) (he2 _ _ (hnorm ω hω u hau hub.le))

end SLEExactGauge.Multipoint

end

end OAI
