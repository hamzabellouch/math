import OAI.Probability.SLE.LoewnerCharts
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! Compact-test continuity extends to every terminal-integrable weight.
This permits weighted inverse-chart tests whose supports approach the old
boundary, using domination by the Radon terminal mass. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge

local instance dominatedTestLocallyCompact : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma integral_test_distance_le_of_domination
    (μ ν : Measure upperHalfPlane) (hμ : μ ≤ ν)
    (f g : upperHalfPlane → ℝ) (hf : Integrable f ν) (hg : Integrable g ν) :
    dist (∫ z, f z ∂μ) (∫ z, g z ∂μ) ≤ ∫ z, ‖f z-g z‖ ∂ν := by
  rw [Real.dist_eq,← integral_sub (hf.mono_measure hμ) (hg.mono_measure hμ)]
  calc
    |∫ z, f z-g z ∂μ| ≤ ∫ z, ‖f z-g z‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => f z-g z)
    _ ≤ _ := integral_mono_measure hμ (ae_of_all _ (fun _ => norm_nonneg _)) (hf.sub hg).norm

/-- Monotonicity is not needed: domination and compact-test continuity suffice. -/
theorem continuous_integral_of_radon_domination
    (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane) [ν.Regular]
    (hdom : ∀ t, N t ≤ ν)
    (hcont : ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂N t))
    (g : upperHalfPlane → ℝ) (hg : Integrable g ν) :
    Continuous (fun t => ∫ z, g z ∂N t) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨f,hfs,herr,hfc,hfi⟩ := hg.exists_hasCompactSupport_integral_sub_le
    (show 0 < ε/3 by positivity)
  let φ : C_c(upperHalfPlane,ℝ) := ⟨⟨f,hfc⟩,hfs⟩
  have hct : ContinuousAt (fun u => ∫ z, φ z ∂N u) t := (hcont φ).continuousAt
  have hnear := (Metric.tendsto_nhds.mp hct) (ε/3)
    (show 0 < ε/3 by positivity)
  filter_upwards [hnear] with s hs
  have hb (u : ℝ≥0) : dist (∫ z, g z ∂N u) (∫ z, f z ∂N u) ≤ ε/3 :=
    (integral_test_distance_le_of_domination (N u) ν (hdom u) g f hg hfi).trans herr
  have h1 := dist_triangle (∫ z, g z ∂N s) (∫ z, f z ∂N s) (∫ z, g z ∂N t)
  have h2 := dist_triangle (∫ z, f z ∂N s) (∫ z, f z ∂N t) (∫ z, g z ∂N t)
  change dist (∫ z, f z ∂N s) (∫ z, f z ∂N t) < ε/3 at hs
  rw [dist_comm (∫ z, f z ∂N t) (∫ z, g z ∂N t)] at h2
  linarith [hb s,hb t]

theorem continuous_lintegral_of_radon_domination
    (N : ℝ≥0 → Measure upperHalfPlane) (ν : Measure upperHalfPlane) [ν.Regular]
    (hdom : ∀ t, N t ≤ ν)
    (hcont : ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂N t))
    (g : upperHalfPlane → ℝ≥0∞) (hg : Measurable g) (hfin : ∫⁻ z, g z ∂ν ≠ ∞) :
    Continuous (fun t => ∫⁻ z, g z ∂N t) := by
  have hreal : Integrable (fun z => (g z).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top hg.aemeasurable hfin
  have hc := continuous_integral_of_radon_domination N ν hdom hcont _ hreal
  have he (t : ℝ≥0) : ENNReal.ofReal (∫ z, (g z).toReal ∂N t) = ∫⁻ z, g z ∂N t := by
    rw [ofReal_integral_eq_lintegral_ofReal (hreal.mono_measure (hdom t))
      (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))]
    apply lintegral_congr_ae
    have hfinite : ∀ᵐ z ∂ν, g z ≠ ∞ := (ae_lt_top hg hfin).mono (fun _ h => h.ne)
    filter_upwards [ae_mono (hdom t) hfinite] with z hz
    exact ENNReal.ofReal_toReal hz
  simpa only [Function.comp_def,he] using ENNReal.continuous_ofReal.comp hc

end SLEExactGauge

end

end OAI
