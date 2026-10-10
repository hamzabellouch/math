import OAI.Analysis.IrrationalRotation.Model.CompactTransfer
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Invariant233.UniformlyAbsolutelyContinuous

variable {X ι : Type*} [MeasurableSpace X]

theorem mono {μ : Measure X} {ν η : ι → Measure X}
    (hν : UniformlyAbsolutelyContinuous μ ν) (hην : ∀ i, η i ≤ ν i) :
    UniformlyAbsolutelyContinuous μ η := by
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hν ε hε
  exact ⟨δ, hδ, fun A hA hμ i => (hην i A).trans_lt (hsmall A hA hμ i)⟩

theorem restrict {μ : Measure X} {ν : ι → Measure X}
    (hν : UniformlyAbsolutelyContinuous μ ν) (s : ι → Set X) :
    UniformlyAbsolutelyContinuous μ (fun i => (ν i).restrict (s i)) :=
  hν.mono (fun _ => Measure.restrict_le_self)

theorem map_restrict {Z : Type*} [MeasurableSpace Z]
    {μ : Measure X} {ν : ι → Measure Z} (f : Z → X) (hf : Measurable f)
    (hν : UniformlyAbsolutelyContinuous μ (fun i => (ν i).map f))
    (s : ι → Set Z) :
    UniformlyAbsolutelyContinuous μ (fun i => ((ν i).restrict (s i)).map f) :=
  hν.mono (fun _ => Measure.map_mono Measure.restrict_le_self hf)

theorem tendsto_apply_of_base_tendsto_zero
    {μ : Measure X} {ν : ι → Measure X}
    (hν : UniformlyAbsolutelyContinuous μ ν)
    {L : Filter ι} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hbase : Tendsto (fun i => μ (s i)) L (𝓝 0)) :
    Tendsto (fun i => ν i (s i)) L (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  obtain ⟨δ, hδ, hsmall⟩ := hν η (ENNReal.coe_pos.mp hη)
  have hδ' : (0 : ℝ≥0∞) < δ := ENNReal.coe_pos.mpr hδ
  filter_upwards [hbase.eventually_lt_const hδ'] with i hi
  exact (hsmall (s i) (hs i) hi i).le.trans hηε.le

theorem tendsto_real_apply_of_base_tendsto_zero
    {μ : Measure X} {ν : ι → Measure X}
    (hν : UniformlyAbsolutelyContinuous μ ν)
    {L : Filter ι} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hbase : Tendsto (fun i => μ (s i)) L (𝓝 0)) :
    Tendsto (fun i => (ν i).real (s i)) L (𝓝 0) := by
  simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hν.tendsto_apply_of_base_tendsto_zero s hs hbase)

theorem tendsto_real_apply_of_base_real_tendsto_zero
    {μ : Measure X} [IsFiniteMeasure μ] {ν : ι → Measure X}
    (hν : UniformlyAbsolutelyContinuous μ ν)
    {L : Filter ι} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hbase : Tendsto (fun i => μ.real (s i)) L (𝓝 0)) :
    Tendsto (fun i => (ν i).real (s i)) L (𝓝 0) := by
  apply hν.tendsto_real_apply_of_base_tendsto_zero s hs
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbase
  simpa only [Function.comp_def, Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _),
    ENNReal.ofReal_zero] using h

end Invariant233.UniformlyAbsolutelyContinuous

end OAI
