import OAI.Probability.SLE.Geometry.LocalCrosscutSides
import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! Actual first exits forced by the waypoint route.  Compactness of the
finite time window gives an attained first exit, strictly after the early
surviving prefix. No stopping-time or exit-location assumption is used. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.CrosscutSides

theorem exists_first_domain_exit
    {X : Type*} [TopologicalSpace X] (D : Set X) (hD : IsOpen D)
    (ζ : ℝ → X) {a L : ℝ}
    (hc : ContinuousOn ζ (Icc 0 L)) (hearly : MapsTo ζ (Icc 0 a) D)
    (hhit : ∃ t ∈ Icc (0 : ℝ) L, ζ t ∉ D) :
    ∃ τ ∈ Ioc a L, ζ τ ∉ D ∧ MapsTo ζ (Ico 0 τ) D := by
  let K := Icc (0 : ℝ) L ∩ ζ ⁻¹' Dᶜ
  have hKc : IsClosed K := hc.preimage_isClosed_of_isClosed isClosed_Icc hD.isClosed_compl
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset hKc inter_subset_left
  have hKn : K.Nonempty := by
    obtain ⟨t, ht, hh⟩ := hhit
    exact ⟨t, ht, hh⟩
  obtain ⟨τ, hτ, hmin⟩ := hK.exists_isLeast hKn
  have haτ : a < τ := by
    by_contra hh
    exact hτ.2 (hearly ⟨hτ.1.1, le_of_not_gt hh⟩)
  refine ⟨τ, ⟨haτ, hτ.1.2⟩, hτ.2, ?_⟩
  intro t ht
  by_contra hh
  exact (not_le_of_gt ht.2) (hmin ⟨⟨ht.1, ht.2.le.trans hτ.1.2⟩, hh⟩)

theorem first_domain_exit_unique
    {X : Type*} (D : Set X) (ζ : ℝ → X) {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ)
    (hτout : ζ τ ∉ D) (hσout : ζ σ ∉ D)
    (hτin : MapsTo ζ (Ico 0 τ) D) (hσin : MapsTo ζ (Ico 0 σ) D) : τ = σ := by
  apply le_antisymm
  · by_contra hh
    exact hσout (hτin ⟨hσ, lt_of_not_ge hh⟩)
  · by_contra hh
    exact hτout (hσin ⟨hτ, lt_of_not_ge hh⟩)

theorem waypoint_first_exit_after_early_prefix
    (γ : ℝ≥0 → ℂ) (hγ : Continuous γ) (T : ℝ≥0)
    (ζ : ℝ → ℂ) (hc : ContinuousOn ζ (Icc 0 3))
    (hearly : MapsTo ζ (Icc 0 2) (survivingDomain γ T))
    (hhit : ∃ s ∈ Icc 0 T, ∃ t ∈ Icc (0 : ℝ) 3, γ s = ζ t) :
    ∃ τ ∈ Ioc (2 : ℝ) 3, ζ τ ∉ survivingDomain γ T ∧
      MapsTo ζ (Ico 0 τ) (survivingDomain γ T) := by
  apply exists_first_domain_exit (survivingDomain γ T) (isOpen_survivingDomain hγ T)
    ζ hc hearly
  obtain ⟨s, hs, t, ht, he⟩ := hhit
  refine ⟨t, ht, ?_⟩
  intro hh
  exact hh.1.2 ⟨s, hs, he⟩

/-- A continuous nonzero side-coordinate cannot change sign before exit. -/
theorem exit_prefix_positive
    {X : Type*} [TopologicalSpace X] {D : Set X} (j : X → ℝ)
    (hj : ContinuousOn j D) (ζ : ℝ → X) {a τ : ℝ}
    (hc : ContinuousOn ζ (Ico a τ)) (hin : MapsTo ζ (Ico a τ) D)
    (hn : ∀ t ∈ Ico a τ, j (ζ t) ≠ 0) (haτ : a < τ)
    (hstart : 0 < j (ζ a)) : ∀ t ∈ Ico a τ, 0 < j (ζ t) :=
  positive_on_preconnected_of_nonzero isPreconnected_Ico (hj.comp hc hin)
    hn ⟨le_rfl, haτ⟩ hstart

theorem exit_prefix_negative
    {X : Type*} [TopologicalSpace X] {D : Set X} (j : X → ℝ)
    (hj : ContinuousOn j D) (ζ : ℝ → X) {a τ : ℝ}
    (hc : ContinuousOn ζ (Ico a τ)) (hin : MapsTo ζ (Ico a τ) D)
    (hn : ∀ t ∈ Ico a τ, j (ζ t) ≠ 0) (haτ : a < τ)
    (hstart : j (ζ a) < 0) : ∀ t ∈ Ico a τ, j (ζ t) < 0 :=
  negative_on_preconnected_of_nonzero isPreconnected_Ico (hj.comp hc hin)
    hn ⟨le_rfl, haτ⟩ hstart

end SLEExactGauge.CrosscutSides

end

end OAI
