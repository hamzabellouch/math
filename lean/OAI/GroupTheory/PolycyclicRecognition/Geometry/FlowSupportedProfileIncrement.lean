import OAI.GroupTheory.PolycyclicRecognition.Analysis.OccupationCompactRestriction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowSampleDomination
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SampledProfileIncrements
import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationLimitSelection

namespace OAI

/-! # Supported profile increments from one fixed occupation limit

The cutoff is chosen before the occupation limit, which is chosen before
the microstep length. Invariance and the stationary estimate remain explicit
interfaces to the already proved Cartan occupation and stationary theorems.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set Metric
open scoped Topology NNReal

theorem supported_profile_increment_of_flow
    {V W A G ι : Type*} [MetricSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace A] [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G]
    {Λ Kπ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (S : Set C(V, W)) (hS : IsCompact S) [MeasurableSpace S] [BorelSpace S]
    (π : G →* Multiplicative W) (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    {l : Filter ι} [l.NeBot]
    (samples : ι → ProbabilityMeasure A) (profile : ι → A → S)
    (hprofile : ∀ i, Measurable (profile i)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun i => ProbabilityMeasure.map (samples i) (profile i)) l (𝓝 ν))
    (m : Measure V) [m.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts m]
    (Fs : ι → C(V × ℝ, V)) (F : C(V × ℝ, V)) (hF : Tendsto Fs l (𝓝 F))
    (hpres : ∀ i t, MeasurePreserving (fun z => Fs i (z, t)) m m)
    (chart : ι → A × V → NormalizedPair G Λ) (hchart : ∀ i, Measurable (chart i))
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (r : ι → ℝ) (hr : Tendsto r l atTop) {T : ℝ} (hT : 0 < T)
    (hmove : ∀ i a z t, (d (r i * t))⁻¹ • chart i (a, z) = chart i (a, Fs i (z, t)))
    (hidentity : ∀ i, ∀ᵐ a ∂(samples i : Measure A), ∀ z,
      (r i * T)⁻¹ • pairHeight π (d (r i * T)) (chart i (a, z)) =
      T⁻¹ • ((profile i a).val (Fs i (z, T)) - (profile i a).val z))
    {U : Set V} (hU : IsOpen U) (z : V) (hseg : ∀ t ∈ Icc 0 T, F (z, t) ∈ U)
    (hinvariant : ∀ (ρ : C(V, ℝ)) (hi : Integrable ρ m) (hp : ∀ x, 0 ≤ ρ x)
      (hm : ∫ x, ρ x ∂m = 1), HasCompactSupport ρ → tsupport ρ ⊆ U →
      ∀ (u : Ultrafilter ι), (u : Filter ι) ≤ l →
      ∀ μ : ProbabilityMeasure (NormalizedPair G Λ),
      Tendsto (fun i => productOccupationLaw (samples i)
        (densityProbabilityMeasure m ρ hi hp hm) (chart i)) u (𝓝 μ) →
      SMulInvariantMeasure G (NormalizedPair G Λ) (μ : Measure _))
    {B : Set W} (hB : IsCompact B) {b : W} (hb : b ∈ B)
    (hconvex : IsClosed (convexHull ℝ B))
    (hstationary : ∀ μ : ProbabilityMeasure (NormalizedPair G Λ),
      SMulInvariantMeasure G (NormalizedPair G Λ) (μ : Measure _) →
      Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
        infDist ((L : ℝ)⁻¹ • pairHeight π (d L) p) B ∂(μ : Measure _)) atTop (𝓝 0))
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    T⁻¹ • (f.val (F (z, T)) - f.val z) ∈ convexHull ℝ B := by
  obtain ⟨η, ρ, c, hηcomp, hρcomp, hρU, hηpos, hρpos, hηz, hηi, hρi,
    hηmass, hρmass, hbound⟩ := exists_flow_probability_cutoffs m Fs F hF z hT.le hU hseg
  let ηlaw := densityProbabilityMeasure m η hηi hηpos hηmass
  let μs := fun i => productOccupationLaw (samples i)
    (densityProbabilityMeasure m ρ hρi hρpos hρmass) (chart i)
  obtain ⟨u, μ, hul, hμ, hνu⟩ := exists_occupation_limit_preserving μs hν
  have hinv := hinvariant ρ hρi hρpos hρmass hρcomp hρU u hul μ hμ
  let K := tsupport η
  have hKm : MeasurableSet K := (isClosed_tsupport η).measurableSet
  have hηfull : ∀ᵐ x ∂(ηlaw : Measure V), x ∈ K :=
    ae_mem_densityProbabilityMeasure m η hηi hηpos hηmass K
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  let ηK := supportedProbabilityRestriction ηlaw K hKm hηfull
  let chartK := fun i (p : A × K) => chart i (p.1, p.2.val)
  have hchartK (i : ι) : Measurable (chartK i) :=
    (hchart i).comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have hlaws (i : ι) : productOccupationLaw (samples i) ηK (chartK i) =
      productOccupationLaw (samples i) ηlaw (chart i) :=
    productOccupationLaw_supportedRestriction (samples i) ηlaw K hKm hηfull (chart i) (hchart i)
  have hdom := microstep_sample_laws_dominated m samples η ρ hηi hρi hηpos hρpos
    hηmass hρmass ρ.continuous.measurable r
    (hr.eventually (eventually_gt_atTop 0)) hT.le (fun i p => Fs i p) hpres chart hchart
    d hd0 hmul hmove c hbound
  have hdomu : ∀ L : ℕ, 0 < L → ∀ᶠ i in (u : Filter ι), ∀ j : Fin ⌊r i * T / (L : ℝ)⌋₊,
      Measure.map (fun p : NormalizedPair G Λ => (d L ^ (j : ℕ))⁻¹ • p)
        (productOccupationLaw (samples i) ηK (chartK i) : Measure _) ≤ c • (μs i : Measure _) := by
    intro L hL
    filter_upwards [(hdom L hL).filter_mono hul] with i hi
    simpa only [hlaws] using hi
  have hzK : z ∈ K := subset_tsupport η hηz.ne'
  have hzsup : (⟨z, hzK⟩ : K) ∈ (ηK : Measure K).support :=
    mem_support_supportedProbabilityRestriction ηlaw K hKm hηfull
      (mem_support_densityProbabilityMeasure m η η.continuous hηi hηpos hηmass hηz)
  have ht : Tendsto (fun i => r i * T) u atTop :=
    (hr.atTop_mul_const hT).mono_left hul
  exact sampled_profile_increment_mem S hS K hηcomp π hπ samples profile hprofile ν hνu
    ηK chartK hchartK μs μ hμ d hd hd0 hmul _ ht c hdomu T⁻¹ (ContinuousMap.id V)
    (fun i => flowTimeSlice (Fs i) T) (flowTimeSlice F T)
    ((flowTimeSlice_tendsto hF T).mono_left hul)
    (fun i => (hidentity i).mono (fun a ha x => ha x.val))
    hB hb hconvex (hstationary μ hinv) hf hzsup

end PolycyclicRecognition

end

end OAI
