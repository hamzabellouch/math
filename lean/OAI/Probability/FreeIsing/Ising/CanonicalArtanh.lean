import OAI.Probability.FreeIsing.Ising.CanonicalMartingales

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation PosteriorCompensatorStopping ArtanhMartingaleFormula

lemma canonicalCovarianceEnergy_uniformObservation_real {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (r : ℝ) (hr : 0 ≤ r) (q : IsingInnovation.State d ℝ) :
    canonicalCovarianceEnergy beta v r.toNNReal (uniformObservation q) =
      gibbsCovarianceEnergy beta v (fun _ s u => WienerSampler.sample u s) (r, q) := by
  unfold canonicalCovarianceEnergy gibbsCovarianceEnergy
  apply tsum_congr
  intro w
  apply congrArg (fun z : ℝ => z ^ 2)
  apply congrArg (infiniteGibbsCovariance beta v w)
  funext i
  change WienerSampler.sample (q.2 i) r.toNNReal +
    (r.toNNReal : ℝ) * spinSign (q.1 i) =
      r * spinSign (q.1 i) + WienerSampler.sample (q.2 i) r.toNNReal
  rw [Real.coe_toNNReal r hr, add_comm]

 theorem canonicalCovarianceEnergy_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Paths d => canonicalCovarianceEnergy beta v p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  let B : TreeVertex d → ℝ≥0 → ℝ → ℝ := fun _ s u => WienerSampler.sample u s
  have hmB (i : TreeVertex d) (s : ℝ≥0) : Measurable (B i s) :=
    (continuous_eval_const s).measurable.comp WienerSampler.measurable_sample
  let f : ℝ × Paths d → ℝ := fun p => canonicalCovarianceEnergy beta v p.1.toNNReal p.2
  have hf : Measurable f := by
    have hn : Measurable (fun p : ℝ × Paths d => (p.1.toNNReal, p.2)) :=
      (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
    have hc : Measurable (fun p : ℝ≥0 × Paths d => canonicalCovarianceEnergy beta v p.1 p.2) :=
      (stronglyMeasurable_joint_of_isStronglyProgressive
        (canonicalCovarianceEnergy_progressive beta v)).measurable
    exact Measurable.comp
      (g := fun p : ℝ≥0 × Paths d => canonicalCovarianceEnergy beta v p.1 p.2)
      (f := fun p : ℝ × Paths d => (p.1.toNNReal, p.2)) hc hn
  have hp := (MeasurePreserving.id (volume.restrict (Ioc (0 : ℝ) T))).prod
    (measurePreserving_uniformObservation μ)
  apply (hp.integrable_comp hf.aestronglyMeasurable).mp
  have hi := (hμ.infiniteGibbsCovariance_timeEnergy
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal) hmB
    (fun _ u => (WienerSampler.sample u).continuous) v T.coe_nonneg).2.2.2.1
  change Integrable (gibbsCovarianceEnergy beta v B) _ at hi
  apply hi.congr
  have hmem : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (labelMeasure d))),
      p.1 ∈ Ioc (0 : ℝ) T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  exact (canonicalCovarianceEnergy_uniformObservation_real beta v p.1 hp.1.le p.2).symm

 theorem canonical_posterior_initial_zero
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    posterior beta v 0 =ᵐ[observationLaw μ] 0 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply (ae_map_iff measurable_uniformObservation.aemeasurable
    (measurableSet_eq_fun (measurable_posterior beta v 0) measurable_const)).mpr
  filter_upwards [infiniteGibbsSpinMean_brownian_zero beta μ
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)] with q hq
  exact (posterior_uniformObservation beta v 0 q).trans (hq v)

 theorem continuousPosterior_initial_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    continuousPosterior beta v 0 =ᵐ[observationLaw μ] 0 :=
  ((continuousPosterior_modification hd hμ hb hcrit v).2 0).trans
    (canonical_posterior_initial_zero hμ v)

def canonicalResponseDrift {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ :=
  posterior beta v t x * infiniteGibbsResponseRow beta v (fun i => x i t)

lemma canonicalResponseDrift_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (canonicalResponseDrift beta v) :=
  (posterior_progressive beta v).mul
    (isStronglyProgressive_infiniteGibbsResponseRow _ beta v _ evaluation_progressive)

def canonicalPosteriorExit {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    ℕ → Paths d → WithTop ℝ≥0 :=
  jointExit (continuousPosterior beta v) (canonicalCovarianceCompensator beta v)

 theorem canonicalPosteriorExit_localizing
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    IsLocalizingSequence (filtration d).rightCont (canonicalPosteriorExit beta v) (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply LocalizedArtanhFormula.isLocalizingSequence_jointExit_primitive
    (continuousPosterior_progressive beta v) (canonicalCovarianceEnergy_progressive beta v)
    (fun n => by simpa only [NNReal.coe_natCast] using canonicalCovarianceEnergy_integrable hμ v n)
  filter_upwards [(continuousPosterior_modification hd hμ hb hcrit v).1] with x hx
  intro T
  obtain ⟨r, hr0, hr1, hr⟩ := PosteriorInteriorLocalization.exists_uniform_radius_of_compact
    (s := Icc (0 : ℝ≥0) T) isCompact_Icc hx.continuousOn
    (fun t _ => continuousPosterior_interior beta v t x)
  exact ⟨r, hr1, fun t ht => hr t ⟨zero_le, ht⟩⟩

 theorem canonical_artanh_decomposition
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d)
    (n : ℕ) (T : ℝ≥0) :
    let τ := canonicalPosteriorExit beta v n
    let N := stoppedProcess (continuousPosterior beta v) τ
    ∃ L : Paths d → ℝ, StronglyMeasurable L ∧ MemLp L 2 (observationLaw μ) ∧
      Tendsto (fun k => ∫ x,
        (BrownianGrid.uniformSum N (fun t x => firstWeight (N t x)) T k x - L x) ^ 2
          ∂observationLaw μ) atTop (𝓝 0) ∧
      stoppedProcess (continuousField beta v) τ T =ᵐ[observationLaw μ]
        (fun x => L x + stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta v)) τ T x) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨L, hmL, hL, hl, he⟩ := LocalizedArtanhFormula.exists_jointExit_artanh_decomposition
    (continuousPosterior_martingale hd hμ hb hcrit v)
    (continuousPosterior_compensatedSquare_martingale hd hμ hb hcrit v)
    (continuousPosterior_progressive beta v) (canonicalCovarianceEnergy_progressive beta v)
    (continuousPosterior_modification hd hμ hb hcrit v).1
    (continuousPosterior_initial_zero hd hμ hb hcrit v)
    (Eventually.of_forall (fun x t => (abs_lt.mpr (continuousPosterior_interior beta v t x)).le))
    (Eventually.of_forall (fun x t => tsum_nonneg (fun _ => sq_nonneg _)))
    (canonicalCovarianceEnergy_integrable hμ v) n T
  have hd1 := ArtanhResponseCoefficients.ae_all_primitive_eq_responseDrift beta v evaluation
    evaluation_progressive (continuousPosterior_progressive beta v)
    (continuousPosterior_modification hd hμ hb hcrit v).2
  have hd2 := ae_all_nnrealTimePrimitive_eq_of_modification
    ((continuousPosterior_progressive beta v).mul
      (isStronglyProgressive_infiniteGibbsResponseRow _ beta v _ evaluation_progressive))
    (canonicalResponseDrift_progressive beta v)
    (fun t => ((continuousPosterior_modification hd hμ hb hcrit v).2 t).mono
      (fun x hx => congrArg (fun r => r * infiniteGibbsResponseRow beta v (fun i => x i t)) hx))
  refine ⟨L, hmL, hL, hl, ?_⟩
  filter_upwards [he, continuousPosterior_initial_zero hd hμ hb hcrit v, hd1, hd2]
    with x hx hz h1 h2
  simp only [hz, Pi.zero_apply, Real.artanh_zero, sub_zero] at hx
  change Real.artanh (continuousPosterior beta v _ x) = _ at hx
  rw [artanh_continuousPosterior] at hx
  refine hx.trans ?_
  congr 1
  exact (h1 _).trans (h2 _)

end Problem367.IsingObservationFactor

end

end OAI
