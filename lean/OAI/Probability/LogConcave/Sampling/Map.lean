import Mathlib
import OAI.Probability.LogConcave.Model

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling

theorem TVAtMost.map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ ν : Measure E} {ε : ℝ} (h : TVAtMost μ ν ε)
    {f : E → F} (hf : Measurable f) : TVAtMost (μ.map f) (ν.map f) ε := by
  intro s hs
  simpa only [Measure.real, Measure.map_apply hf hs] using h (f ⁻¹' s) (hs.preimage hf)

end LogConcaveSampling

namespace LogConcaveSampling
lemma prob_prod_event_lower {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set (X × Y)} (hs : MeasurableSet s) {a : ℝ}
    (h : ∀ y, a ≤ μ.real ((fun x => (x,y)) ⁻¹' s)) : a ≤ (μ.prod ν).real s := by
  have h' : ENNReal.ofReal a ≤ (μ.prod ν) s := by
    rw [Measure.prod_apply_symm hs]
    calc
      _ = ∫⁻ _ : Y, ENNReal.ofReal a ∂ν := by simp
      _ ≤ _ := lintegral_mono (fun y =>
        (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mpr (h y))
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (μ.prod ν) s)).mp h'
end LogConcaveSampling

end LowerProof
end
end
end

end OAI
