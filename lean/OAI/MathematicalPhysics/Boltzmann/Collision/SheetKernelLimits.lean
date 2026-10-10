import OAI.MathematicalPhysics.Boltzmann.Branching.SmallFirstGain
import OAI.MathematicalPhysics.Boltzmann.Branching.LargeOutput

namespace OAI

/-! # Kernel limits for the manuscript's probability mixtures of sheets -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.SheetClass
open BoltzmannNonuniqueness.SheetMixtures

namespace BoltzmannNonuniqueness.SheetKernelLimits

theorem mixture_region_bound {ι : Type*} [MeasurableSpace ι] {ν : Measure ι}
    [IsProbabilityMeasure ν] {M : ι → Measure Velocity} (hM : Measurable M)
    (q : ℝ) (v : Velocity) {S : Set Coordinates} (hS : MeasurableSet S) {B : ℝ≥0∞}
    (hb : ∀ᵐ i ∂ν, normalizedMeasure (M i) q v S ≤ B) :
    normalizedMeasure (ν.bind M) q v S ≤ B := by
  rw [normalized_bind_apply ν hM q v hS]
  exact (lintegral_mono_ae hb).trans_eq (by simp)

theorem dominated_region_bound {ι : Type*} [MeasurableSpace ι] {ν : Measure ι}
    [IsProbabilityMeasure ν] {M : ι → Measure Velocity} (hM : Measurable M)
    (q : ℝ) (v : Velocity) {S : Set Coordinates} (hS : MeasurableSet S) {A B : ℝ≥0∞}
    (hb : ∀ᵐ i ∂ν, normalizedMeasure (M i) q v S ≤ B)
    {c : Measure Velocity} (hdom : c ≤ A • ν.bind M) :
    normalizedMeasure c q v S ≤ A * B := by
  have h := measure_mono_incoming hdom (fun ξ => ENNReal.ofReal (H q ξ / H q v)) v S
  rw [ChartKernel.measure_smul, Measure.smul_apply, smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl (mixture_region_bound hM q v hS hb))

theorem mixture_large_output {q L ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ {ι : Type*} [MeasurableSpace ι] (ν : Measure ι)
      [IsProbabilityMeasure ν] (M : ι → Measure Velocity), Measurable M →
      (∀ᵐ i ∂ν, IsElementary L (M i)) → ∀ (v : Velocity), transverse v ≠ 0 → R < ‖v‖ →
      normalizedMeasure (ν.bind M) q v univ ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR, hb⟩ := LargeOutput.uniform_large_output (L := L) hq₁ hq₂ hε
  refine ⟨R, hR, ?_⟩
  intro ι inst ν hprob M hM hc v hv hvR
  apply mixture_region_bound hM q v .univ
  filter_upwards [hc] with i hi
  obtain ⟨d, ρ, hd, hdmax, hρprob, hρ, he⟩ := hi
  rw [he]
  exact hb d ρ hρprob hd hdmax hρ v hv hvR

theorem mixture_axis_input {q L δ ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {ι : Type*} [MeasurableSpace ι] (ν : Measure ι)
      [IsProbabilityMeasure ν] (M : ι → Measure Velocity), Measurable M →
      (∀ᵐ i ∂ν, IsElementary L (M i)) → ∀ (v : Velocity), transverse v ≠ 0 →
      ‖transverse v‖ ≤ η → normalizedMeasure (ν.bind M) q v (AxisInput.away v δ) ≤ ENNReal.ofReal ε := by
  obtain ⟨η, hη, hb⟩ := AxisInput.uniform_axis_input (L := L) hq₁ hq₂ hδ hε
  refine ⟨η, hη, ?_⟩
  intro ι inst ν hprob M hM hc v hv hvη
  apply mixture_region_bound hM q v (AxisInput.measurableSet_away v δ)
  filter_upwards [hc] with i hi
  obtain ⟨d, ρ, hd, hdmax, hρprob, hρ, he⟩ := hi
  rw [he]
  exact hb d ρ hρprob hd hdmax hρ v hv hvη

theorem mixture_axis_mismatch {q L δ ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {ι : Type*} [MeasurableSpace ι] (ν : Measure ι)
      [IsProbabilityMeasure ν] (M : ι → Measure Velocity), Measurable M →
      (∀ᵐ i ∂ν, IsElementary L (M i)) → ∀ (v : Velocity), transverse v ≠ 0 →
      ‖transverse v‖ ≤ η → normalizedMeasure (ν.bind M) q v
        (AxisMismatch.incoming v δ ×ˢ univ) ≤ ENNReal.ofReal ε := by
  obtain ⟨η, hη, hb⟩ := AxisMismatch.uniform_axis_mismatch (L := L) hq₁ hq₂ hδ hε
  refine ⟨η, hη, ?_⟩
  intro ι inst ν hprob M hM hc v hv hvη
  apply mixture_region_bound hM q v ((AxisMismatch.measurableSet_incoming v δ).prod .univ)
  filter_upwards [hc] with i hi
  obtain ⟨d, ρ, hd, hdmax, hρprob, hρ, he⟩ := hi
  rw [he]
  exact hb d ρ hρprob hd hdmax hρ v hv hvη

/-- The actual elementary subclass with a prescribed upper transverse width. -/
def IsThinElementary (L η : ℝ) (c : Measure Velocity) : Prop :=
  ∃ (d : ℝ) (ρ : Measure ℝ), 0 ≤ d ∧ d ≤ min η (1 / 8) ∧ IsProbabilityMeasure ρ ∧
    AxialMoment ρ L ∧ c = sheetLaw d ρ

theorem measurableSet_smallRegion (v : Velocity) (δ : ℝ) :
    MeasurableSet (SmallInputLimit.smallRegion v δ) :=
  measurableSet_lt ((measurable_transverse.comp (measurable_point v)).norm) measurable_const

theorem mixture_small_input {q L r ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hr : 0 < r) (hε : 0 < ε) :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧ ∀ {ι : Type*} [MeasurableSpace ι] (ν : Measure ι)
      [IsProbabilityMeasure ν] (M : ι → Measure Velocity), Measurable M →
      (∀ᵐ i ∂ν, IsThinElementary L η (M i)) → ∀ (v : Velocity), r ≤ ‖transverse v‖ →
      ∀ δ' : ℝ, δ' ≤ δ → normalizedMeasure (ν.bind M) q v
        (SmallInputLimit.smallRegion v δ') ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, η, hδ, hη, hb⟩ := SmallInputLimit.uniform_small_input (L := L) hq₁ hq₂ hr hε
  refine ⟨δ, η, hδ, hη, ?_⟩
  intro ι inst ν hprob M hM hc v hv δ' hδ'
  apply (measure_mono (show SmallInputLimit.smallRegion v δ' ⊆ SmallInputLimit.smallRegion v δ from
    fun _ hy => lt_of_lt_of_le hy hδ')).trans
  apply mixture_region_bound hM q v (measurableSet_smallRegion v δ)
  filter_upwards [hc] with i hi
  obtain ⟨d, ρ, hd, hdmax, hρprob, hρ, he⟩ := hi
  rw [he]
  exact hb d ρ hρprob hd hdmax hρ v hv

end BoltzmannNonuniqueness.SheetKernelLimits

end

end OAI
