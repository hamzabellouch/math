import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BoundedGlobalHeight
import OAI.Analysis.RieszRectifiability.Projections.ProjectionSingularMoments

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_global_height_with_local_singular_limits {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (w : ℕ → Ambient d → ℝ) (hwm : ∀ j, Measurable (w j))
    (hw : ∀ H j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B E : ℕ → ℝ)
    (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE : ∀ H j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, w (φ j) x ^ 2
        ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
        Tendsto (fun j => ∫ x, w (φ j) x * ψ x
          ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
        (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
          ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
          ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
            ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H ∧
        ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
          Tendsto (fun j => ∫ q : Ambient d × Ambient d,
            fractionalBilinear (p + 1) (w (φ j)) ψ q.1 q.2
            ∂(((σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)).prod
              ((σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)))) atTop
            (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f ψ q.1 q.2
              ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
                ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))) := by
  obtain ⟨φ, hφ, f, hfm, hf, hsecond, hmoment⟩ := exists_bounded_global_projection_height
    e π K Q he hπ hleft σ hlocal C hC
    (by simpa only [Fintype.card_fin] using! hlower) hdiam w hw B E hB
    (by simpa only [Fintype.card_fin] using! henergy)
    (by simpa only [Fintype.card_fin] using! hE)
  refine ⟨φ, hφ, f, hfm, hf, hsecond, hmoment, ?_⟩
  intro H
  let s := boundedProjectionRegion π (e 0) K H
  let I := exhaustionBox (Fin (p + 1)) H
  let μ := fun j => boundedProjectionFiniteMeasure (σ (φ j)) π (e 0) K H
  have hplane : (coordinatePlaneMeasure e).restrict s = boxPlaneMeasure I e :=
    coordinatePlaneMeasure_restrict_boundedRegion e π K he hπ.continuous hleft H
  have hνball : ∀ᵐ x ∂boxPlaneMeasure I e, x ∈ ball (e 0) (planeBoxOuterRadius K H) := by
    rw [← hplane]
    filter_upwards [ae_restrict_mem (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet]
      with x hx
    exact hx.2
  have hμball : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)), x ∈ ball (e 0) (planeBoxOuterRadius K H) := by
    intro j
    filter_upwards [ae_restrict_mem (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet]
      with x hx
    exact hx.2
  have hmcompact : ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
      Tendsto (fun j => ∫ x, w (φ j) x * ψ x ∂(μ j : Measure (Ambient d))) atTop
        (𝓝 (∫ x, f x * ψ x ∂boxPlaneMeasure I e)) := by
    intro ψ L A hc hLip hA
    have hm := hmoment H ψ L A hc hLip hA
    change Tendsto (fun j => ∫ x, w (φ j) x * ψ x ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, f x * ψ x ∂(coordinatePlaneMeasure e).restrict s)) at hm
    rwa [hplane] at hm
  have hm := compact_moments_extend_on_ball (fun j => (μ j : Measure (Ambient d)))
    (boxPlaneMeasure I e) (e 0) (planeBoxOuterRadius K H) hμball hνball (fun j => w (φ j)) f hmcompact
  have hgμ : ∀ j, GlobalUpperGrowth (p + 1) G (μ j : Measure (Ambient d)) := by
    intro j
    refine ⟨(hg (φ j)).1, ?_⟩
    intro x r hr
    have hle : (μ j : Measure (Ambient d)) ≤ σ (φ j) := Measure.restrict_le_self
    exact (hle (ball x r)).trans ((hg (φ j)).2 x r hr)
  have hheight := boundedProjectionFiniteMeasure_height_of_AD_lower e π K Q he hπ hleft
    σ hlocal C hC (by simpa only [Fintype.card_fin] using! hlower) hdiam H
  have hfH : MemLp f 2 (boxPlaneMeasure I e) := by
    have h := hf H
    change MemLp f 2 ((coordinatePlaneMeasure e).restrict s) at h
    rwa [hplane] at h
  have hresult := projection_singular_limit_of_moments p I e π K Q he hπ hleft μ
    ((boundedProjectionFiniteMeasure_tendsto e π K Q he hπ hleft σ hlocal H).comp hφ.tendsto_atTop)
    G hgμ (fun j => boundedProjectionRegion_ae_coordinates (σ (φ j)) π hπ.continuous (e 0) K H)
    (fun k => hφ.tendsto_atTop.eventually (hheight k)) (fun j => w (φ j)) f
    (fun j => hw H (φ j)) (fun j => hwm (φ j)) hfH hfm (fun ψ D hLip _ _ => hm ψ D hLip)
    (B H) (E H) (fun j => hB H (φ j)) (fun j => henergy H (φ j)) (fun j => hE H (φ j))
  change _ ∧ _ ∧ _ at hresult
  simpa only [← hplane] using! hresult

end

end RieszRectifiability

end OAI
