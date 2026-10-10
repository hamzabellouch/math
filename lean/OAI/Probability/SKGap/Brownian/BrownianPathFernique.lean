import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section

noncomputable section
namespace SKGap.PathBridge
open MeasureTheory ProbabilityTheory Real Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
abbrev UnitInterval := Set.Icc (0:ℝ) 1
abbrev UnitPath := C(UnitInterval,ℝ)
instance pathMeasurable : MeasurableSpace UnitPath := borel _
instance pathBorel : BorelSpace UnitPath := ⟨rfl⟩

def pathPairEvaluations (p : UnitPath × UnitPath) : ℕ→ℝ×ℝ :=
  fun k=>(p.1 (denseSeq UnitInterval k),p.2 (denseSeq UnitInterval k))

lemma continuous_pathPairEvaluations : Continuous pathPairEvaluations := by
  apply continuous_pi
  intro k
  exact ((ContinuousMap.evalCLM ℝ (denseSeq UnitInterval k)).continuous.comp continuous_fst).prodMk
    ((ContinuousMap.evalCLM ℝ (denseSeq UnitInterval k)).continuous.comp continuous_snd)

lemma injective_pathPairEvaluations : Function.Injective pathPairEvaluations := by
  intro p q h
  apply Prod.ext
  · apply ContinuousMap.coe_injective
    apply (denseRange_denseSeq UnitInterval).equalizer p.1.continuous q.1.continuous
    funext k
    exact congrArg Prod.fst (congrFun h k)
  · apply ContinuousMap.coe_injective
    apply (denseRange_denseSeq UnitInterval).equalizer p.2.continuous q.2.continuous
    funext k
    exact congrArg Prod.snd (congrFun h k)

lemma measurableEmbedding_pathPairEvaluations : MeasurableEmbedding pathPairEvaluations :=
  continuous_pathPairEvaluations.measurableEmbedding injective_pathPairEvaluations

lemma centered_gaussian_path_rotation (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (hG : IsGaussianProcess (fun t : UnitInterval=>fun f : UnitPath=>f t) μ)
    (h0 : ∀ t : UnitInterval, ∫ f : UnitPath,f t ∂μ=0) (θ : ℝ) :
    (μ.prod μ).map (ContinuousLinearMap.rotation θ)=μ.prod μ := by
  apply measurableEmbedding_pathPairEvaluations.map_injective
  rw [Measure.map_map continuous_pathPairEvaluations.measurable (by fun_prop)]
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (continuous_pathPairEvaluations.measurable.comp (by fun_prop)).aemeasurable
    continuous_pathPairEvaluations.measurable.aemeasurable).2
  intro s
  let e : UnitPath→s→ℝ := fun f i=>f (denseSeq UnitInterval i)
  have he : Measurable e := by
    apply Measurable.of_eval
    intro i
    exact (ContinuousMap.evalCLM ℝ (denseSeq UnitInterval i)).continuous.measurable
  have heG : HasGaussianLaw e μ := (hG.comp_right (denseSeq UnitInterval)).hasGaussianLaw s
  let ν := μ.map e
  let : IsGaussian ν := heG.isGaussian_map
  have hν0 : (∫ x : s→ℝ,id x ∂ν)=0 := by
    rw [show ν=μ.map e from rfl,integral_map he.aemeasurable measurable_id.aestronglyMeasurable]
    ext i
    have hh := (ContinuousLinearMap.proj i : (s→ℝ)→L[ℝ]ℝ).integral_comp_comm heG.integrable
    exact hh.symm.trans (h0 _)
  have hr := IsGaussian.map_rotation_eq_self (μ:=ν) hν0 θ
  let pair : ((s→ℝ)×(s→ℝ))→s→ℝ×ℝ := fun p i=>(p.1 i,p.2 i)
  have hp : Measurable pair := by fun_prop
  have hr' := congrArg (Measure.map pair) hr
  rw [Measure.map_map hp (by fun_prop)] at hr'
  have hn : ν.prod ν=(μ.prod μ).map (Prod.map e e) := Measure.map_prod_map μ μ he he
  rw [hn,Measure.map_map (hp.comp (by fun_prop)) (he.prodMap he),
    Measure.map_map hp (he.prodMap he)] at hr'
  convert hr' using 1
  · congr 1
  · rfl

theorem centered_gaussian_path_fernique (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (hG : IsGaussianProcess (fun t : UnitInterval=>fun f : UnitPath=>f t) μ)
    (h0 : ∀ t : UnitInterval, ∫ f : UnitPath,f t ∂μ=0) :
    ∃ a : ℝ, 0<a ∧ Integrable (fun f : UnitPath=>exp (a*‖f‖^2)) μ :=
  exists_integrable_exp_sq_of_map_rotation_eq_self
    (centered_gaussian_path_rotation μ hG h0 (-(π/4)))
end SKGap.PathBridge

end
end

section

noncomputable section
namespace SKGap.PathBridge
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
    (brownian_unit_continuous hB) (fun _=>hB.integral_eval _)
end SKGap.PathBridge

end
end

end OAI
