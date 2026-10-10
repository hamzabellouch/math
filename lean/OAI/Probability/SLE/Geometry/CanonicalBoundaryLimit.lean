import OAI.Probability.SLE.Loewner.CanonicalTraceCandidate
import OAI.Probability.SLE.Loewner.TargetBoundaryLimit
import OAI.Probability.SLE.Geometry.FiniteParameterProjection

namespace OAI

/-! A continuous canonical trace modification with the exact inverse-tip
limit simultaneously at every time, obtained from an actual source witness. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance boundaryRealMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance boundaryRealBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance boundaryComplexMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance boundaryComplexBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
local instance boundaryDriverPolish : PolishSpace Target.Driver :=
  ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace
local instance boundaryDriverMetric : MetricSpace Target.Driver :=
  TopologicalSpace.metrizableSpaceMetric Target.Driver

theorem exists_canonical_all_time_boundary_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    ∃ Ψ : Target.Driver → C(ℝ≥0,ℂ), Measurable Ψ ∧
      (∀ ω, Ψ (Target.normalizedDriver κ B hc h0 ω)=sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
      ∀ᵐ b ∂W, Ψ b 0=0 ∧ (∀ T, 0 ≤ (Ψ b T).im) ∧
        ∀ T, Tendsto (fun y => Target.rawTipAt κ T y b) (𝓝[>] 0) (𝓝 (Ψ b T)) := by
  have : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Ψ,hΨ,hΨeq,_⟩ := exists_canonical_trace_candidate_modification
    κ hκ hκ8 B hB hm hc h0 γ G F hw W hW
  let p (T : ℝ≥0) (b : Target.Driver) : Prop :=
    Ψ b 0=0 ∧ 0 ≤ (Ψ b T).im ∧
      Tendsto (fun y => Target.rawTipAt κ T y b) (𝓝[>] 0) (𝓝 (Ψ b T))
  have hEval : Measurable (fun q : ℝ≥0 × Target.Driver => Ψ q.2 q.1) :=
    continuous_eval.measurable.comp ((hΨ.comp measurable_snd).prodMk measurable_fst)
  have hEval0 : Measurable (fun q : ℝ≥0 × Target.Driver => Ψ q.2 0) :=
    ((continuous_eval_const 0).measurable.comp hΨ).comp measurable_snd
  have hp : MeasurableSet {q : ℝ≥0 × Target.Driver | p q.1 q.2} :=
    (measurableSet_eq_fun hEval0 measurable_const).inter
      ((measurableSet_le measurable_const hEval.im).inter
        (Target.joint_measurableSet_rawTipAt_tendsto κ hκ _ hEval))
  have hLaw := Target.normalizedDriver_law κ hκ B hB hm hc h0 W hW
  have hsource : ∀ᵐ ω ∂P, ∀ T, p T (Target.normalizedDriver κ B hc h0 ω) := by
    apply ae_of_all
    intro ω T
    have he (t : ℝ≥0) : Ψ (Target.normalizedDriver κ B hc h0 ω) t=γ ω t := by
      have h := congrArg (fun e : C(ℝ≥0,ℂ) => e t) (hΨeq ω)
      simpa only [sourceTracePath,ContinuousMap.coe_mk] using h
    refine ⟨(he 0).trans (hw ω).2.1,?_,?_⟩
    · rw [he]
      exact (hw ω).2.2.1 T
    · simpa only [he] using Target.rawTipAt_tendsto_witness κ hκ
        (Target.normalizedDriver κ B hc h0 ω) (fun t => Real.sqrt κ*B t ω)
        (γ ω) (G ω) (F ω) (hw ω) (Target.normalizedDriver_matches κ hκ B hc h0 ω) T
  have hall := ae_forall_parameter_of_hasLaw hLaw p hp hsource
  refine ⟨Ψ,hΨ,hΨeq,?_⟩
  filter_upwards [hall] with b hb
  exact ⟨(hb 0).1,fun T => (hb T).2.1,fun T => (hb T).2.2⟩

end SLEExactGauge

end

end OAI
