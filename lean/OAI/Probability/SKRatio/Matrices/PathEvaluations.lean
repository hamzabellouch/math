import Mathlib
import OAI.Probability.SKRatio.Matrices.UnitInterval

namespace OAI

section
section
noncomputable section
namespace SKRatioGaussian.PathBridge
open MeasureTheory ProbabilityTheory Real Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology

def pathEvaluations (f : UnitPath) : ℕ→ℝ := fun k=>f (denseSeq UnitInterval k)
lemma measurableEmbedding_pathEvaluations : MeasurableEmbedding pathEvaluations := by
  apply Continuous.measurableEmbedding
  · apply continuous_pi
    intro k
    exact (ContinuousMap.evalCLM ℝ (denseSeq UnitInterval k)).continuous
  · intro p q h
    apply ContinuousMap.coe_injective
    apply (denseRange_denseSeq UnitInterval).equalizer p.continuous q.continuous
    exact h

variable {Ω : Type*} [MeasurableSpace Ω]

def continuousPathVersion (X : UnitInterval→Ω→ℝ) (ω : Ω) : UnitPath := by
  classical
  exact if h : Continuous (fun t=>X t ω) then ⟨fun t=>X t ω,h⟩ else 0

lemma continuousPathVersion_eval {μ : Measure Ω} {X : UnitInterval→Ω→ℝ}
    (hc : ∀ᵐ ω ∂μ,Continuous (fun t=>X t ω)) (t : UnitInterval) :
    (fun ω=>continuousPathVersion X ω t)=ᵐ[μ] X t := by
  filter_upwards [hc] with ω hω
  simp only [continuousPathVersion,dite_eq_left hω,ContinuousMap.coe_mk]

lemma aemeasurable_continuousPathVersion {μ : Measure Ω} {X : UnitInterval→Ω→ℝ}
    (hX : ∀ t,AEMeasurable (X t) μ)
    (hc : ∀ᵐ ω ∂μ,Continuous (fun t=>X t ω)) :
    AEMeasurable (continuousPathVersion X) μ := by
  apply measurableEmbedding_pathEvaluations.aemeasurable_comp_iff.mp
  apply AEMeasurable.of_eval
  intro k
  exact (hX _).congr (continuousPathVersion_eval hc _).symm

lemma gaussian_continuousPathVersion {μ : Measure Ω} {X : UnitInterval→Ω→ℝ}
    (hG : IsGaussianProcess X μ)
    (hc : ∀ᵐ ω ∂μ,Continuous (fun t=>X t ω)) :
    IsGaussianProcess (fun t : UnitInterval=>fun f : UnitPath=>f t)
      (μ.map (continuousPathVersion X)) := by
  have hm := aemeasurable_continuousPathVersion hG.aemeasurable hc
  have hv := hG.congr (fun t=>(continuousPathVersion_eval hc t).symm)
  constructor
  intro I
  have he : Measurable (fun f : UnitPath=>I.restrict (fun t=>f t)) := by
    apply Measurable.of_eval
    intro t
    exact (show Continuous (fun f : UnitPath=>f (t:UnitInterval)) from
      (ContinuousMap.evalCLM ℝ (t:UnitInterval)).continuous).measurable
  refine ⟨he.aemeasurable, ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable he.aemeasurable hm]
  exact (hv.hasGaussianLaw I).isGaussian_map

lemma mean_continuousPathVersion {μ : Measure Ω} {X : UnitInterval→Ω→ℝ}
    (hX : ∀ t,AEMeasurable (X t) μ)
    (hc : ∀ᵐ ω ∂μ,Continuous (fun t=>X t ω)) (t : UnitInterval) :
    (∫ f : UnitPath,f t ∂μ.map (continuousPathVersion X))=∫ ω,X t ω ∂μ := by
  have he : Measurable (fun f : UnitPath=>f t) :=
    (show Continuous (fun f : UnitPath=>f t) from (ContinuousMap.evalCLM ℝ t).continuous).measurable
  rw [integral_map (aemeasurable_continuousPathVersion hX hc) he.aestronglyMeasurable]
  exact integral_congr_ae (continuousPathVersion_eval hc t)

theorem continuous_gaussian_process_fernique {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : UnitInterval→Ω→ℝ} (hG : IsGaussianProcess X μ)
    (hc : ∀ᵐ ω ∂μ,Continuous (fun t=>X t ω))
    (h0 : ∀ t,∫ ω,X t ω ∂μ=0) :
    ∃ a : ℝ, 0<a ∧ Integrable (fun ω=>exp (a*‖continuousPathVersion X ω‖^2)) μ := by
  have hm := aemeasurable_continuousPathVersion hG.aemeasurable hc
  let : IsProbabilityMeasure (μ.map (continuousPathVersion X)) :=
    (Measure.isProbabilityMeasure_map_iff hm).2 inferInstance
  obtain ⟨a,ha,hi⟩ := centered_gaussian_path_fernique (μ.map (continuousPathVersion X))
    (gaussian_continuousPathVersion hG hc) (fun t=>by
      rw [mean_continuousPathVersion hG.aemeasurable hc,h0])
  refine ⟨a,ha,?_⟩
  exact (integrable_map_measure (by fun_prop) hm).mp hi

def unitBrownianProcess (B : ℝ≥0→Ω→ℝ) : UnitInterval→Ω→ℝ :=
  fun t=>B ⟨t.1,t.2.1⟩

lemma brownian_unit_gaussian {P : Measure Ω} {B : ℝ≥0→Ω→ℝ}
    (hB : IsBrownianReal B P) : IsGaussianProcess (unitBrownianProcess B) P :=
  hB.isGaussianProcess.comp_right (fun t : UnitInterval=>⟨t.1,t.2.1⟩)

lemma brownian_unit_continuous {P : Measure Ω} {B : ℝ≥0→Ω→ℝ}
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P,Continuous (fun t=>unitBrownianProcess B t ω) := by
  filter_upwards [hB.cont] with ω hω
  exact hω.comp (by fun_prop)

theorem brownian_unit_fernique {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0→Ω→ℝ} (hB : IsBrownianReal B P) :
    ∃ a : ℝ, 0<a ∧ Integrable
      (fun ω=>exp (a*‖continuousPathVersion (unitBrownianProcess B) ω‖^2)) P :=
  continuous_gaussian_process_fernique (brownian_unit_gaussian hB)
    (brownian_unit_continuous hB) (fun time=>hB.integral_eval ⟨time.1,time.2.1⟩)
end SKRatioGaussian.PathBridge

end
end

section

noncomputable section

end
end
end

end OAI
