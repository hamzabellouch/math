import Mathlib

namespace OAI

section
section
noncomputable section
namespace SKRatioGaussian.PathBridge
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
end SKRatioGaussian.PathBridge

end
end

section

noncomputable section

end
end
end

end OAI
