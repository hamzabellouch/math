import OAI.Probability.SLE.Gauge.RibbonStoppedMassTransport

namespace OAI

/-! Transfer a completed-ribbon experiment through the actual SLE scaling
law on continuous traces. No uniform step estimate is reapplied to a chart
whose spatial scale varies with the number of strips. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates ScaleTraceLaw RibbonPassageScaling

local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma ribbonStoppedMass_scale_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (c : ℝ≥0) (hc : 0 < c)
    (hlaw : μ.map (fun ω => scalePath c (f ω)) = μ.map f)
    (P : ℂ → ℂ)
    (he : Topology.IsClosedEmbedding (fun z : closedRibbon => (c : ℂ) * P z))
    (g g' : C(ℂ, ℝ)) (hgg' : ∀ z : ℂ, g' ((c : ℂ) * z) = g z)
    (k ε κ : ℝ) {v : ℝ} (hv : 0 < v) (D : Set ℂ) (b : ℝ≥0∞) :
    μ {ω | f ω ∈ ribbonStoppedMassEvent P g k ε κ v D b} ≤
      μ {ω | f ω ∈ ribbonStoppedMassEvent (fun z => (c : ℂ) * P z) g' k ε κ
        ((c : ℝ) * v) (affine 0 c '' D) (ENNReal.ofReal ((c : ℝ) ^ dimension κ) * b)} := by
  let E := ribbonStoppedMassEvent (fun z => (c : ℂ) * P z) g' k ε κ
    ((c : ℝ) * v) (affine 0 c '' D) (ENNReal.ofReal ((c : ℝ) ^ dimension κ) * b)
  have hE : MeasurableSet E := measurableSet_ribbonStoppedMassEvent _ he g' k ε κ _ _ _
  calc
    _ ≤ μ {ω | scalePath c (f ω) ∈ E} := measure_mono (fun ω hω =>
      mem_ribbonStoppedMassEvent_scalePath c hc (f ω) P g g' hgg' k ε κ hv D b hω)
    _ = (μ.map (fun ω => scalePath c (f ω))) E :=
      (Measure.map_apply ((measurable_scalePath c).comp hf) hE).symm
    _ = (μ.map f) E := by rw [hlaw]
    _ = _ := Measure.map_apply hf hE

end SLEExactGauge

end

end OAI
