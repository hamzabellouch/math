import OAI.Probability.SLE.Mass.RadonProcessAEUniqueness
import OAI.Probability.SLE.LoewnerCharts
import OAI.Probability.SLE.Mass.RadonTestFamily

namespace OAI

/-! Equality of nonnegative tests yields equality of random Radon measures
on one common event, using the existing countable determining family. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported NNReal ENNReal

namespace SLEExactGauge

lemma random_halfPlane_measure_eq_of_lintegrals
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N M : Ω → Measure upperHalfPlane)
    (hN : ∀ ω, (N ω).Regular) (hM : ∀ ω, (M ω).Regular)
    (htest : ∀ f : C_c(upperHalfPlane,ℝ), (∀ z, 0 ≤ f z) →
      ∀ᵐ ω ∂P, (∫⁻ z, ENNReal.ofReal (f z) ∂N ω)=∫⁻ z, ENNReal.ofReal (f z) ∂M ω) :
    ∀ᵐ ω ∂P, N ω=M ω := by
  let : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
  have h := random_radon_process_eq_of_positive_tests P (localTestFamily upperHalfPlane)
    (fun _ => N) (fun _ => M) (fun _ => hN) (fun _ => hM) (fun f hf => ?_)
  · exact h.mono (fun _ hω => hω 0)
  · filter_upwards [htest f hf] with ω hω
    intro _
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) f.continuous.measurable.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) f.continuous.measurable.aestronglyMeasurable,hω]

end SLEExactGauge

end

end OAI
