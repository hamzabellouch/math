import OAI.Probability.BenjaminiSchramm.PeakSurgeryProbability

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {E : Type*}

lemma small_frontier_probability_lower (p : unitInterval)
    (A : Set (Set E)) (Z : Set E → ℝ≥0∞) (hZ : Measurable Z)
    (a M N : ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M) (hN : 0 < N)
    (hlower : ENNReal.ofReal a ≤ law p A)
    (hmoment : (∫⁻ ω, Z ω ∂law p) ≤ ENNReal.ofReal M)
    (hscale : 2*M ≤ N*a) :
    ENNReal.ofReal (a/2) ≤ law p (A ∩ {ω | Z ω ≤ ENNReal.ofReal N}) := by
  let B : Set (Set E) := {ω | Z ω ≤ ENNReal.ofReal N}
  have hB : MeasurableSet B := measurableSet_le hZ measurable_const
  have hbad : law p (A \ B) ≤ ENNReal.ofReal (M/N) := by
    calc
      _ ≤ law p {ω | ENNReal.ofReal N ≤ Z ω} := measure_mono fun ω hω => by
        have hh : ¬ Z ω ≤ ENNReal.ofReal N := hω.2
        exact le_of_not_ge hh
      _ ≤ (∫⁻ ω, Z ω ∂law p)/ENNReal.ofReal N :=
        meas_ge_le_lintegral_div hZ.aemeasurable
          (ENNReal.ofReal_ne_zero_iff.mpr hN) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M/ENNReal.ofReal N := ENNReal.div_le_div_right hmoment _
      _ = _ := (ENNReal.ofReal_div_of_pos hN).symm
  have hbadreal : (law p).real (A \ B) ≤ M/N := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    rwa [ENNReal.toReal_ofReal (div_nonneg hM hN.le)] at hh
  have hlowreal : a ≤ (law p).real A := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hlower
    rwa [ENNReal.toReal_ofReal ha] at hh
  have hdiv : M/N ≤ a/2 := (div_le_iff₀ hN).mpr (by nlinarith)
  have hsplit := measureReal_sdiff_add_inter (μ := law p) (s := A) hB
  apply ENNReal.ofReal_le_of_le_toReal
  change a/2 ≤ (law p).real (A ∩ B)
  linarith

end Percolation.BenjaminiSchramm

end

end OAI
