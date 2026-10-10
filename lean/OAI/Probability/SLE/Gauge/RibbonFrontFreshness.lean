import OAI.Probability.SLE.Gauge.RibbonCoordinateGeometry
import OAI.Probability.SLE.Loewner.FreshTipMapOut

namespace OAI

/-! First arrival at a ribbon front is fresh in the actual Loewner sense:
the current tip survives every strictly earlier hull. This identifies the
access prime end with the current driving point through the proved fresh-tip
chart limit. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

theorem ribbon_front_tip_survives_prior
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (hescape : Tendsto (fun s : ℝ => ‖P (s : ℂ)‖) atTop atTop)
    (γ x : ℝ≥0 → ℂ) (T : ℝ≥0) (hx : ContinuousOn x (Icc 0 T))
    (hx0 : (x 0).re = 0) (hcoords : MapsTo x (Icc 0 T) closedRibbon)
    (hγ : EqOn γ (P ∘ x) (Icc 0 T))
    (hfront : ∀ t : ℝ≥0, t < T → (x t).re < (x T).re)
    (hinterior : |(x T).im| < 1) :
    ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s := by
  intro s hs
  have hxs := hx.mono (Icc_subset_Icc_right hs.le)
  have hrex : ContinuousOn (fun t => (x t).re) (Icc 0 s) :=
    Complex.continuous_re.comp_continuousOn hxs
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (show (0 : ℝ≥0) ≤ s from bot_le)) hrex
  let k := (x t).re
  have hk : 0 ≤ k := by
    have hh := hmax (show (0 : ℝ≥0) ∈ Icc 0 s from ⟨le_rfl, bot_le⟩)
    change (x 0).re ≤ (x t).re at hh
    simpa only [hx0] using hh
  have hpast : γ '' Icc 0 s ⊆ P '' {z ∈ closedRibbon | z.re ≤ k} := by
    rintro z ⟨u, hu, rfl⟩
    refine ⟨x u, ⟨hcoords ⟨hu.1, hu.2.trans hs.le⟩, hmax hu⟩, ?_⟩
    exact (hγ ⟨hu.1, hu.2.trans hs.le⟩).symm
  have htip : x T ∈ futureRibbon k :=
    ⟨hfront t (ht.2.trans_lt hs), hinterior⟩
  have hsurv := futureRibbon_survives P hP hi hk hH γ s hpast
    (futureRibbon_unbounded_of_centerline_escape P k hescape)
    (mem_image_of_mem P htip)
  rw [hγ ⟨bot_le, le_rfl⟩]
  exact hsurv

/-- The actual capacity chart tends to the current driver along the
surviving domain at a first ribbon front. -/
theorem IsCapacityTwoWitness.ribbon_front_chart_tendsto
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (hH : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane)
    (hescape : Tendsto (fun s : ℝ => ‖P (s : ℂ)‖) atTop atTop)
    (x : ℝ≥0 → ℂ) (T : ℝ≥0) (hT : 0 < T) (hx : ContinuousOn x (Icc 0 T))
    (hx0 : (x 0).re = 0) (hcoords : MapsTo x (Icc 0 T) closedRibbon)
    (hγ : EqOn γ (P ∘ x) (Icc 0 T))
    (hfront : ∀ t : ℝ≥0, t < T → (x t).re < (x T).re)
    (hinterior : |(x T).im| < 1) :
    Tendsto (G T) (𝓝[survivingDomain γ T] (γ T)) (𝓝 (U T : ℂ)) := by
  exact hw.fresh_tip_chart_tendsto hU hT
    (ribbon_front_tip_survives_prior P hP hi hH hescape γ x T hx hx0 hcoords hγ hfront hinterior)

end SLEExactGauge.RibbonCoordinates

end

end OAI
