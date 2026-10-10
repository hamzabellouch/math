import OAI.Probability.SLE.Geometry.CanonicalBoundaryLimit

namespace OAI

/-! Holomorphicity of the raw inverse under the canonical Wiener law.
Clipping the endpoint inside the half-plane makes differentiability a Borel
condition on a continuous function space. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance inverseHolomorphicMapMeasurable : MeasurableSpace C(ℂ,ℂ) := borel _
local instance inverseHolomorphicMapBorel : BorelSpace C(ℂ,ℂ) := ⟨rfl⟩
local instance inverseHolomorphicDriverPolish : PolishSpace Target.Driver :=
  ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace
local instance inverseHolomorphicDriverMetric : MetricSpace Target.Driver :=
  TopologicalSpace.metrizableSpaceMetric Target.Driver

def upperClip (η : ℝ) (z : ℂ) : ℂ := ⟨z.re,max η z.im⟩

lemma continuous_upperClip (η : ℝ) : Continuous (upperClip η) := by
  convert (Complex.continuous_ofReal.comp Complex.continuous_re).add
    ((Complex.continuous_ofReal.comp ((continuous_const (y := η)).max Complex.continuous_im)).mul
      (continuous_const (y := Complex.I))) using 1
  funext z
  apply Complex.ext <;> simp [upperClip]

lemma upperClip_eq {η : ℝ} {z : ℂ} (h : η ≤ z.im) : upperClip η z=z := by
  apply Complex.ext
  · rfl
  · exact max_eq_right h

def clippedRawInverse (κ : ℝ) (hκ : 0 < κ) (j : ℕ)
    (q : ℝ≥0 × Target.Driver) : C(ℂ,ℂ) :=
  ⟨fun z => Target.inverseFlow κ q.2 (κ.toNNReal*q.1) (upperClip (1/((j:ℝ)+1)) z),
    (Target.continuousOn_inverseFlow κ hκ q.2 (κ.toNNReal*q.1)).comp_continuous
      (continuous_upperClip _) (fun z => (show 0 < (1:ℝ)/((j:ℝ)+1) by positivity).trans_le
        (le_max_left _ _))⟩

lemma measurable_clippedRawInverse (κ : ℝ) (hκ : 0 < κ) (j : ℕ) :
    Measurable (clippedRawInverse κ hκ j) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro z
  exact @Measurable.comp (ℝ≥0 × Target.Driver) (ℝ≥0 × (Target.Driver × ℂ)) ℂ
    inferInstance inferInstance inferInstance
    (fun q => Target.inverseFlow κ q.2.1 q.1 q.2.2)
    (fun q => (κ.toNNReal*q.1,(q.2,upperClip (1/((j:ℝ)+1)) z)))
    (Target.measurable_inverseFlow κ)
    ((measurable_const.mul measurable_fst).prodMk (measurable_snd.prodMk measurable_const))

lemma clippedRawInverse_eventuallyEq (κ : ℝ) (hκ : 0 < κ) (j : ℕ)
    (q : ℝ≥0 × Target.Driver) (z : ℂ) (hz : 1/((j:ℝ)+1) < z.im) :
    (clippedRawInverse κ hκ j q : ℂ → ℂ) =ᶠ[𝓝 z]
      Target.inverseFlow κ q.2 (κ.toNNReal*q.1) := by
  have hn : {w : ℂ | 1/((j:ℝ)+1) < w.im} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  filter_upwards [hn] with w hw
  change Target.inverseFlow κ q.2 (κ.toNNReal*q.1) (upperClip _ w)=_
  rw [upperClip_eq hw.le]

lemma ae_canonical_inverse_holomorphic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    ∀ᵐ b ∂W, ∀ T : ℝ≥0,
      DifferentiableOn ℂ (Target.inverseFlow κ b (κ*T)) upperHalfPlane := by
  have : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hDiff : MeasurableSet {q : C(ℂ,ℂ) × ℂ | DifferentiableAt ℂ q.1 q.2} :=
    measurableSet_of_differentiableAt_with_param ℂ continuous_eval
  have hfixed (j : ℕ) : MeasurableSet {q : ((ℝ≥0 × ℂ) × Target.Driver) |
      1/((j:ℝ)+1) < q.1.2.im →
        DifferentiableAt ℂ (clippedRawInverse κ hκ j (q.1.1,q.2)) q.1.2} := by
    have hlt : MeasurableSet {q : ((ℝ≥0 × ℂ) × Target.Driver) |
        1/((j:ℝ)+1) < q.1.2.im} :=
      measurableSet_lt measurable_const measurable_fst.snd.im
    have hd := hDiff.preimage
      (((measurable_clippedRawInverse κ hκ j).comp
        (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd)
    convert hlt.compl.union hd using 1
    ext q
    simp only [mem_union,mem_compl_iff,mem_ofPred_eq,mem_preimage,Function.comp_apply,
      imp_iff_not_or]
  have hsource (j : ℕ) : ∀ᵐ ω ∂P, ∀ r : ℝ≥0 × ℂ,
      1/((j:ℝ)+1) < r.2.im → DifferentiableAt ℂ
        (clippedRawInverse κ hκ j (r.1,Target.normalizedDriver κ B hc h0 ω)) r.2 := by
    apply ae_of_all
    rintro ω ⟨T,z⟩ hz
    have hzH : z ∈ upperHalfPlane := (show 0 < (1:ℝ)/((j:ℝ)+1) by positivity).trans hz
    have hF : DifferentiableAt ℂ (F ω T) z :=
      ((hw ω).2.2.2.2.1 T z hzH).differentiableAt (isOpen_upperHalfPlane.mem_nhds hzH)
    apply hF.congr_of_eventuallyEq
    filter_upwards [clippedRawInverse_eventuallyEq κ hκ j
      (T,Target.normalizedDriver κ B hc h0 ω) z hz,
      isOpen_upperHalfPlane.mem_nhds hzH] with w he hwH
    rw [he,Real.coe_toNNReal _ hκ.le]
    exact Target.inverseFlow_eq_witness κ hκ _ _ _ _ _ (hw ω)
      (Target.normalizedDriver_matches κ hκ B hc h0 ω) T w hwH
  have hLaw := Target.normalizedDriver_law κ hκ B hB hm hc h0 W hW
  have hall (j : ℕ) := ae_forall_parameter_of_hasLaw hLaw
    (fun (r : ℝ≥0 × ℂ) (b : Target.Driver) => 1/((j:ℝ)+1) < r.2.im →
      DifferentiableAt ℂ (clippedRawInverse κ hκ j (r.1,b)) r.2) (hfixed j) (hsource j)
  filter_upwards [ae_all_iff.mpr hall] with b hb T z hz
  obtain ⟨j,hj⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds (show 0 < z.im from hz))).exists
  have h := (hb j (T,z) hj).congr_of_eventuallyEq
    (clippedRawInverse_eventuallyEq κ hκ j (T,b) z hj).symm
  simpa only [NNReal.coe_mul,Real.coe_toNNReal _ hκ.le] using h.differentiableWithinAt

end SLEExactGauge

end

end OAI
