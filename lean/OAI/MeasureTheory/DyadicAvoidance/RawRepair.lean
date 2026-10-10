import OAI.MeasureTheory.DyadicAvoidance.ExpectedRepair
import OAI.MeasureTheory.DyadicAvoidance.PeriodicEnlargement
import OAI.MeasureTheory.DyadicAvoidance.PeriodicEnvelope

namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- Complete analytic passage from a finite random periodic grid construction to
an open periodic hitting set. The hypotheses are precisely the density, stability,
and raw-failure estimates supplied by the combinatorial construction. -/
theorem periodic_hitting_of_raw_construction
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hbad : volume (Gᶜ ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal p)
    (hgood : ∀ x ∈ G,
      μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal (2 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  classical
  choose V hBV hVo hVp hVm using fun ω =>
    Problem310.Aux.exists_open_periodic_envelope (B ω) (hBp ω)
      (ENNReal.ofReal p) (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
  apply periodic_hitting_of_pointwise_failure_bound μ p hp V hVo hVp N hN G hG hbad
  · calc
      (∫⁻ ω, volume (V ω ∩ Icc (0 : ℝ) 1) ∂μ)
          ≤ ∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) + ENNReal.ofReal p ∂μ :=
        lintegral_mono hVm
      _ = (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) + ENNReal.ofReal p := by
        rw [lintegral_add_left (measurable_of_countable _)]
        simp
      _ ≤ ENNReal.ofReal p + ENNReal.ofReal p := add_le_add hBmean le_rfl
      _ = ENNReal.ofReal (2 * p) := by
        rw [← ENNReal.ofReal_add (le_of_lt hp) (le_of_lt hp)]
        congr 1
        ring
  · intro x hx
    calc
      μ {ω | x ∈ exceptionalCenters (V ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
          ≤ μ {ω | x ∈ exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} := by
        apply measure_mono
        intro ω hω
        exact exceptionalCenters_antitone (hBV ω) N _ hω
      _ ≤ ENNReal.ofReal (2 * p) := hgood x hx

end Problem310.Auxiliary

end

end OAI
