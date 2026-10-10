import OAI.Probability.SLE.Mass.DominatedMassTestContinuity
import OAI.Probability.SLE.Mass.TerminalMassTestLimit

namespace OAI

/-! Terminal-integrable weights pass through local exhaustion. This supplies
terminal exhaustion after conformal weighting, including weights whose
support approaches the boundary. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge

local instance exhaustedTestLocallyCompact : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem terminal_integrable_test_tendsto
    (ν : Measure upperHalfPlane) [ν.Regular]
    (N : ℝ≥0 → Measure upperHalfPlane) (hNr : ∀ t, (N t).Regular)
    (hdom : ∀ t, N t ≤ ν)
    (hlim : ∀ K : Set upperHalfPlane, IsCompact K →
      Tendsto (fun t : ℝ≥0 => (ν-N t) K) atTop (𝓝 0))
    (g : upperHalfPlane → ℝ) (hg : Integrable g ν) :
    Tendsto (fun t : ℝ≥0 => ∫ z, g z ∂N t) atTop (𝓝 (∫ z, g z ∂ν)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨f,hfs,herr,hfc,hfi⟩ := hg.exists_hasCompactSupport_integral_sub_le
    (show 0 < ε/3 by positivity)
  let φ : C_c(upperHalfPlane,ℝ) := ⟨⟨f,hfc⟩,hfs⟩
  have hnear := (Metric.tendsto_nhds.mp (terminal_mass_test_tendsto ν N hNr hdom hlim φ))
    (ε/3) (show 0 < ε/3 by positivity)
  filter_upwards [hnear] with t ht
  have ha : dist (∫ z, g z ∂N t) (∫ z, f z ∂N t) ≤ ε/3 :=
    (integral_test_distance_le_of_domination (N t) ν (hdom t) g f hg hfi).trans herr
  have hb : dist (∫ z, g z ∂ν) (∫ z, f z ∂ν) ≤ ε/3 :=
    (integral_test_distance_le_of_domination ν ν le_rfl g f hg hfi).trans herr
  have h1 := dist_triangle (∫ z, g z ∂N t) (∫ z, f z ∂N t) (∫ z, g z ∂ν)
  have h2 := dist_triangle (∫ z, f z ∂N t) (∫ z, f z ∂ν) (∫ z, g z ∂ν)
  change dist (∫ z, f z ∂N t) (∫ z, f z ∂ν) < ε/3 at ht
  rw [dist_comm (∫ z, f z ∂ν) (∫ z, g z ∂ν)] at h2
  linarith

theorem remaining_integrable_test_tendsto_zero
    (ν : Measure upperHalfPlane) [ν.Regular]
    (N : ℝ≥0 → Measure upperHalfPlane) (hNr : ∀ t, (N t).Regular)
    (hdom : ∀ t, N t ≤ ν)
    (hlim : ∀ K : Set upperHalfPlane, IsCompact K →
      Tendsto (fun t : ℝ≥0 => (ν-N t) K) atTop (𝓝 0))
    (g : upperHalfPlane → ℝ) (hg : Integrable g ν) :
    Tendsto (fun t : ℝ≥0 => ∫ z, g z ∂(ν-N t)) atTop (𝓝 0) := by
  have he (t : ℝ≥0) : (∫ z, g z ∂(ν-N t))=(∫ z, g z ∂ν)-(∫ z, g z ∂N t) := by
    let := hNr t
    have hi := integral_add_measure (hg.mono_measure (Measure.sub_le : ν-N t ≤ ν))
      (hg.mono_measure (hdom t))
    rw [sigmaFinite_sub_add_cancel_of_le (hdom t)] at hi
    linarith
  simpa only [he,sub_self] using
    (tendsto_const_nhds (x := ∫ z, g z ∂ν)).sub
      (terminal_integrable_test_tendsto ν N hNr hdom hlim g hg)

theorem remaining_lintegral_tendsto_zero
    (ν : Measure upperHalfPlane) [ν.Regular]
    (N : ℝ≥0 → Measure upperHalfPlane) (hNr : ∀ t, (N t).Regular)
    (hdom : ∀ t, N t ≤ ν)
    (hlim : ∀ K : Set upperHalfPlane, IsCompact K →
      Tendsto (fun t : ℝ≥0 => (ν-N t) K) atTop (𝓝 0))
    (g : upperHalfPlane → ℝ≥0∞) (hg : Measurable g) (hfin : ∫⁻ z, g z ∂ν ≠ ∞) :
    Tendsto (fun t : ℝ≥0 => ∫⁻ z, g z ∂(ν-N t)) atTop (𝓝 0) := by
  have hreal : Integrable (fun z => (g z).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top hg.aemeasurable hfin
  have hfinite : ∀ᵐ z ∂ν, g z ≠ ∞ := (ae_lt_top hg hfin).mono (fun _ h => h.ne)
  have he (t : ℝ≥0) : ENNReal.ofReal (∫ z, (g z).toReal ∂(ν-N t)) =
      ∫⁻ z, g z ∂(ν-N t) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hreal.mono_measure (Measure.sub_le : ν-N t ≤ ν))
      (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))]
    apply lintegral_congr_ae
    filter_upwards [ae_mono (Measure.sub_le : ν-N t ≤ ν) hfinite] with z hz
    exact ENNReal.ofReal_toReal hz
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (remaining_integrable_test_tendsto_zero ν N hNr hdom hlim _ hreal)
  simpa only [Function.comp_def,he,ENNReal.ofReal_zero] using h

end SLEExactGauge

end

end OAI
