import OAI.Probability.SLE.Loewner.CanonicalInverseNonzero
import OAI.Probability.SLE.Loewner.CanonicalSurvival
import OAI.Probability.SLE.Loewner.TargetForwardAnalytic
import OAI.Probability.SLE.Gauge.DenseInfinityCriterion

namespace OAI

/-! Hydrodynamic normalization transfers through countably many spatial
tests, followed by continuity on the open surviving domain. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance hydroDriverPolish : PolishSpace Target.Driver :=
  ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace
local instance hydroDriverMetric : MetricSpace Target.Driver :=
  TopologicalSpace.metrizableSpaceMetric Target.Driver

lemma measurableSet_raw_dense_infinity (κ : ℝ) :
    MeasurableSet {q : ℝ≥0 × Target.Driver |
      DenseInfinityCriterion (fun z => z*(Target.flow κ q.2 z (κ.toNNReal*q.1)-z))
        {z | Target.Surviving κ q.2 z (κ.toNNReal*q.1)} (2*(q.1:ℂ))} := by
  simp only [DenseInfinityCriterion,ofPred_forall,ofPred_exists]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro _hn
  have hm : Measurable (fun q : ℝ≥0 × Target.Driver =>
      (κ.toNNReal*q.1,(q.2,denseSeq ℂ n))) :=
    (measurable_const.mul measurable_fst).prodMk (measurable_snd.prodMk measurable_const)
  have hs := MeasurableSet.preimage
    (f := fun q : ℝ≥0 × Target.Driver => (κ.toNNReal*q.1,(q.2,denseSeq ℂ n)))
    (Target.measurableSet_surviving κ) hm
  have hf : Measurable (fun q : ℝ≥0 × Target.Driver =>
      ‖denseSeq ℂ n*(Target.flow κ q.2 (denseSeq ℂ n) (κ.toNNReal*q.1)-denseSeq ℂ n)
        -2*(q.1:ℂ)‖) := by
    exact ((measurable_const.mul ((Target.measurable_flow κ).comp hm |>.sub measurable_const)).sub
      (measurable_const.mul measurable_fst.coe_nnreal_real.complex_ofReal)).norm
  convert hs.compl.union (measurableSet_le hf
    (measurable_const : Measurable (fun _ : ℝ≥0 × Target.Driver => (1/((k:ℝ)+1))))) using 1
  ext q
  simp only [mem_union,mem_compl_iff,mem_ofPred_eq,mem_preimage,imp_iff_not_or,
    NNReal.coe_mul]

lemma ae_canonical_dense_infinity
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    ∀ᵐ b ∂W, ∀ T : ℝ≥0,
      DenseInfinityCriterion (fun z => z*(Target.flow κ b z (κ*T)-z))
        {z | Target.Surviving κ b z (κ*T)} (2*(T:ℂ)) := by
  have : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let p (T : ℝ≥0) (b : Target.Driver) :=
    DenseInfinityCriterion (fun z => z*(Target.flow κ b z (κ.toNNReal*T)-z))
      {z | Target.Surviving κ b z (κ.toNNReal*T)} (2*(T:ℂ))
  have hsource : ∀ᵐ ω ∂P, ∀ T, p T (Target.normalizedDriver κ B hc h0 ω) := by
    apply ae_of_all
    intro ω T k
    have hnorm := (hw ω).2.2.2.2.2.2.2.2.2.2.2.1 T
    obtain ⟨N,hN⟩ := denseInfinityCriterion_of_tendsto hnorm k
    refine ⟨N,fun n hn hs => ?_⟩
    rw [Real.coe_toNNReal _ hκ.le] at hs ⊢
    have hD := (Target.surviving_iff_witness κ hκ _ _ _ _ _ (hw ω)
      (Target.normalizedDriver_matches κ hκ B hc h0 ω) T _).mp hs
    have he := Target.flow_eq_witness κ hκ _ _ _ _ _ (hw ω)
      (Target.normalizedDriver_matches κ hκ B hc h0 ω) T _ hD
    simpa only [he] using hN n hn hD
  have hall := ae_forall_parameter_of_hasLaw
    (Target.normalizedDriver_law κ hκ B hB hm hc h0 W hW)
    p (measurableSet_raw_dense_infinity κ) hsource
  filter_upwards [hall] with b hb T
  simpa only [p,NNReal.coe_mul,Real.coe_toNNReal _ hκ.le] using hb T

end SLEExactGauge

end

end OAI
