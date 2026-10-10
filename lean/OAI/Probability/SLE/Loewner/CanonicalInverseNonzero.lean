import OAI.Probability.SLE.Loewner.CanonicalInverseHolomorphic
import OAI.Probability.SLE.Geometry.NormalizedMarkedState

namespace OAI

/-! Nonvanishing derivative of the canonical inverse, transferred through
the same measurable clipped functions used for holomorphicity. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance inverseNonzeroMapMeasurable : MeasurableSpace C(ℂ,ℂ) := borel _
local instance inverseNonzeroMapBorel : BorelSpace C(ℂ,ℂ) := ⟨rfl⟩
local instance inverseNonzeroDriverPolish : PolishSpace Target.Driver :=
  ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace
local instance inverseNonzeroDriverMetric : MetricSpace Target.Driver :=
  TopologicalSpace.metrizableSpaceMetric Target.Driver

lemma IsCapacityTwoWitness.inverse_deriv_ne_zero
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w : ℂ) (hwH : w ∈ upperHalfPlane) :
    deriv (F T) w ≠ 0 := by
  have h := hw.inverse_derivative_identity T (F T w) (hw.2.2.2.2.2.2.1 T hwH)
  rw [hw.2.2.2.2.2.2.2.2.1 T w hwH] at h
  intro hn
  rw [hn,zero_mul] at h
  exact zero_ne_one h

lemma ae_canonical_inverse_deriv_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    ∀ᵐ b ∂W, ∀ (T : ℝ≥0) (z : ℂ), z ∈ upperHalfPlane →
      deriv (Target.inverseFlow κ b (κ*T)) z ≠ 0 := by
  have : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hDeriv : Measurable (fun q : C(ℂ,ℂ) × ℂ => deriv (q.1 : ℂ → ℂ) q.2) :=
    measurable_deriv_with_param continuous_eval
  have hfixed (j : ℕ) : MeasurableSet {q : (ℝ≥0 × ℂ) × Target.Driver |
      1/((j:ℝ)+1) < q.1.2.im →
        deriv (clippedRawInverse κ hκ j (q.1.1,q.2) : ℂ → ℂ) q.1.2 ≠ 0} := by
    have hlt : MeasurableSet {q : (ℝ≥0 × ℂ) × Target.Driver |
        1/((j:ℝ)+1) < q.1.2.im} := measurableSet_lt measurable_const measurable_fst.snd.im
    have hmD : Measurable (fun q : (ℝ≥0 × ℂ) × Target.Driver =>
        deriv (clippedRawInverse κ hκ j (q.1.1,q.2) : ℂ → ℂ) q.1.2) :=
      hDeriv.comp (((measurable_clippedRawInverse κ hκ j).comp
        (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd)
    convert hlt.compl.union (measurableSet_eq_fun hmD
      (measurable_const : Measurable (fun _ : (ℝ≥0 × ℂ) × Target.Driver => (0 : ℂ)))).compl using 1
    ext q
    simp only [mem_union,mem_compl_iff,mem_ofPred_eq,imp_iff_not_or]
  have hsource (j : ℕ) : ∀ᵐ ω ∂P, ∀ r : ℝ≥0 × ℂ,
      1/((j:ℝ)+1) < r.2.im → deriv
        (clippedRawInverse κ hκ j (r.1,Target.normalizedDriver κ B hc h0 ω) : ℂ → ℂ) r.2 ≠ 0 := by
    apply ae_of_all
    rintro ω ⟨T,z⟩ hz
    have hzH : z ∈ upperHalfPlane := (show 0 < (1:ℝ)/((j:ℝ)+1) by positivity).trans hz
    have he : (clippedRawInverse κ hκ j (T,Target.normalizedDriver κ B hc h0 ω) : ℂ → ℂ)
        =ᶠ[𝓝 z] F ω T := by
      filter_upwards [clippedRawInverse_eventuallyEq κ hκ j
        (T,Target.normalizedDriver κ B hc h0 ω) z hz,
        isOpen_upperHalfPlane.mem_nhds hzH] with w he hwH
      rw [he,Real.coe_toNNReal _ hκ.le]
      exact Target.inverseFlow_eq_witness κ hκ _ _ _ _ _ (hw ω)
        (Target.normalizedDriver_matches κ hκ B hc h0 ω) T w hwH
    rw [he.deriv_eq]
    exact (hw ω).inverse_deriv_ne_zero T z hzH
  have hLaw := Target.normalizedDriver_law κ hκ B hB hm hc h0 W hW
  have hall (j : ℕ) := ae_forall_parameter_of_hasLaw hLaw
    (fun (r : ℝ≥0 × ℂ) (b : Target.Driver) => 1/((j:ℝ)+1) < r.2.im →
      deriv (clippedRawInverse κ hκ j (r.1,b) : ℂ → ℂ) r.2 ≠ 0) (hfixed j) (hsource j)
  filter_upwards [ae_all_iff.mpr hall] with b hb T z hz
  obtain ⟨j,hj⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds (show 0 < z.im from hz))).exists
  have he := (clippedRawInverse_eventuallyEq κ hκ j (T,b) z hj).deriv_eq
  have h := hb j (T,z) hj
  rw [he] at h
  simpa only [NNReal.coe_mul,Real.coe_toNNReal _ hκ.le] using h

end SLEExactGauge

end

end OAI
