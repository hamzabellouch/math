import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedGainSmoothingAE
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusCharacteristic

namespace OAI

section

/-! # The finite spacetime measure of the fundamental cell -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusKineticChart

def baseVolume (T : ℝ) : Measure Published.SpaceTime :=
  (volume.restrict (Icc 0 T)).prod (volume.restrict TorusChart.cube)

instance (T : ℝ) : IsFiniteMeasure (baseVolume T) := by
  have he := TorusChart.representative_measurePreserving.map_eq
  have : IsFiniteMeasure ((volume : Measure Velocity).restrict TorusChart.cube) := by
    rw [← he]
    exact Measure.isFiniteMeasure_map volume TorusChart.representative
  unfold baseVolume
  infer_instance

theorem baseVolume_le (T : ℝ) : baseVolume T ≤ Published.timeSpaceVolume T :=
  Measure.prod_mono le_rfl Measure.restrict_le_self

theorem cellVolume_eq_base (T : ℝ) : cellVolume T = (baseVolume T).prod volume := rfl

theorem pairCellVolume_eq_base (T : ℝ) : pairCellVolume T = (baseVolume T).prod volume := rfl

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # Uniform integrability of actual localized Euclidean transport sources -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.TorusKineticChart

def region (U : ℝ) : Set KineticPhase := (Icc 0 U ×ˢ TorusChart.cube) ×ˢ univ

theorem measurableSet_region (U : ℝ) : MeasurableSet (region U) :=
  (measurableSet_Icc.prod TorusChart.measurableSet_cube).prod MeasurableSet.univ

theorem cellVolume_eq (U : ℝ) : cellVolume U = (volume : Measure KineticPhase).restrict (region U) := by
  unfold cellVolume region
  calc
    _ = (((volume : Measure ℝ).prod (volume : Measure Velocity)).restrict
        (Icc 0 U ×ˢ TorusChart.cube)).prod ((volume : Measure Velocity).restrict univ) := by
      rw [Measure.restrict_univ,Measure.prod_restrict]
    _ = _ := Measure.prod_restrict _ _

theorem localizedSource_eq {U : ℝ} {χ : KineticPhase → ℝ}
    (hχ : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube}) (f Q : KineticPhase → ℝ) :
    localizedSource U χ f Q = fun z =>
      χ z*(region U).indicator Q z+(transportDerivative χ z+χ z)*(region U).indicator f z := by
  funext z
  by_cases ht : z.1.1 ∈ Icc 0 U
  · by_cases hx : z.1.2 ∈ TorusChart.cube
    · have hz : z ∈ region U := ⟨⟨ht,hx⟩,mem_univ _⟩
      simp only [localizedSource,ite_eq_left ht,indicator_of_mem hz]
    · have hn : z ∉ tsupport χ := fun h => hx (hχ h)
      have hc := image_eq_zero_of_notMem_tsupport hn
      have hd := transportDerivative_eq_zero hn
      simp only [localizedSource,ite_eq_left ht,hc,hd,zero_mul,zero_add]
  · have hz : z ∉ region U := fun h => ht h.1.1
    simp only [localizedSource,ite_eq_right ht,indicator_of_notMem hz,mul_zero,zero_add]

private theorem uniformIntegrable_add {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : ℕ → X → ℝ} (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (fun n x => f n x+g n x) 1 μ := by
  obtain ⟨hu,C,hC⟩ := hf
  obtain ⟨hv,D,hD⟩ := hg
  refine ⟨hu.add hv (by norm_num),C+D,fun n => ?_⟩
  exact (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ 1)).trans
    (by simpa only [ENNReal.coe_add] using add_le_add (hC n) (hD n))

theorem localizedSource_uniformIntegrable {U : ℝ} {χ : KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube})
    {f Q : ℕ → KineticPhase → ℝ}
    (hf : UniformIntegrable f 1 (cellVolume U)) (hQ : UniformIntegrable Q 1 (cellVolume U)) :
    UniformIntegrable (fun n => localizedSource U χ (f n) (Q n)) 1 volume := by
  have hf0 := Compactness.uniformIntegrable_indicator_of_restrict (measurableSet_region U)
    (cellVolume_eq U ▸ hf)
  have hQ0 := Compactness.uniformIntegrable_indicator_of_restrict (measurableSet_region U)
    (cellVolume_eq U ▸ hQ)
  obtain ⟨C,hC⟩ := hχ.continuous.bounded_above_of_compact_support hc
  let D : KineticPhase → ℝ := fun z => transportDerivative χ z+χ z
  have hDm : Continuous D := (transportDerivative_continuous hχ).add hχ.continuous
  have hDc : HasCompactSupport D := (transportDerivative_hasCompactSupport hc).add hc
  obtain ⟨B,hB⟩ := hDm.bounded_above_of_compact_support hDc
  have h1 := Compactness.uniformIntegrable_of_bounded_multiplier hQ0 hχ.continuous.measurable
    (⟨max C 0,le_max_right _ _⟩ : ℝ≥0)
    (fun z => (show |χ z| ≤ C from hC z).trans (le_max_left _ _))
  have h2 := Compactness.uniformIntegrable_of_bounded_multiplier hf0 hDm.measurable
    (⟨max B 0,le_max_right _ _⟩ : ℝ≥0)
    (fun z => (show |D z| ≤ B from hB z).trans (le_max_left _ _))
  have H := uniformIntegrable_add h1 h2
  simpa only [localizedSource_eq hs,D] using H

end BoltzmannNonuniqueness.TorusKineticChart

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.localized_source_ui {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) {χ : Published.KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube}) :
    UniformIntegrable (fun n : ℕ => TransportCutoff.localizedSource F.time χ
      (EuclideanFlight.density q (F.approximation n).solution.value)
      (EuclideanFlight.source (n+1) q (F.approximation n).solution.value)) 1 volume :=
  TorusKineticChart.localizedSource_uniformIntegrable hχ hc hs F.density_ui_cell F.source_ui_cell

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
