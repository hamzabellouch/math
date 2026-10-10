import OAI.Probability.FreeIsing.Estimates.LocalizedArtanhFormula
import OAI.Probability.FreeIsing.Ising.CanonicalContinuousFields
import OAI.Probability.FreeIsing.Ising.CopyEnergyIntegrability

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy PosteriorCompensatorStopping

private lemma continuous_real_tanh : Continuous Real.tanh :=
  lipschitzWith_tanh_response.continuous

def continuousPosterior {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ℝ := Real.tanh (continuousField beta v t x)

lemma continuousPosterior_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousPosterior beta v) := by
  intro T
  exact continuous_real_tanh.comp_stronglyMeasurable (continuousField_progressive beta v T)

lemma continuousPosterior_interior {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : continuousPosterior beta v t x ∈ Ioo (-1 : ℝ) 1 :=
  ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

lemma artanh_continuousPosterior {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) :
    Real.artanh (continuousPosterior beta v t x) = continuousField beta v t x :=
  Real.artanh_tanh _

 theorem continuousPosterior_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    (∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousPosterior beta v t x)) ∧
      (∀ t, continuousPosterior beta v t =ᵐ[observationLaw μ] posterior beta v t) := by
  obtain ⟨hc, he⟩ := continuousField_modification hd hμ hb hcrit v
  refine ⟨hc.mono (fun x hx => continuous_real_tanh.comp hx), fun t => ?_⟩
  filter_upwards [he t, tanh_field_eq_posterior_ae hμ hb v t] with x hx ht
  exact (congrArg Real.tanh hx).trans ht

lemma copyProjection_measurePreserving
    {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (j : Bool) :
    MeasurePreserving (projection (d := d) j) (copies beta μ) (observationLaw μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
    (beta := beta) (μ := μ) (rho := (observationLaw μ).map (innovationMap beta))
    (eta := kernel beta μ) kernel_graphLaw
  cases j
  · exact hr
  · exact hl

def copyContinuousField {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : ℝ := continuousField beta v t (projection j q)

def copyContinuousPosterior {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : ℝ := continuousPosterior beta v t (projection j q)

lemma copyContinuousField_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (copyContinuousField beta v j) := by
  cases j
  · exact ProgressiveVersionPushforward.progressive_version
      (isStronglyProgressive_artanh _ (isStronglyProgressive_infiniteGibbsSpinMean _ beta v _
        IsingConditionalCopyBounds.progressive_rightObservation))
  · exact ProgressiveVersionPushforward.progressive_version
      (isStronglyProgressive_artanh _ (isStronglyProgressive_infiniteGibbsSpinMean _ beta v _
        IsingConditionalCopyBounds.progressive_leftObservation))

lemma copyContinuousPosterior_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (copyContinuousPosterior beta v j) := by
  intro T
  exact continuous_real_tanh.comp_stronglyMeasurable (copyContinuousField_progressive beta v j T)

 theorem copyContinuousPosterior_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) (j : Bool) :
    (∀ᵐ q ∂copies beta μ, Continuous (fun t => copyContinuousPosterior beta v j t q)) ∧
      (∀ t, copyContinuousPosterior beta v j t =ᵐ[copies beta μ]
        (fun q => posterior beta v t (projection j q))) := by
  obtain ⟨hc, he⟩ := continuousPosterior_modification hd hμ hb hcrit v
  have hp := (copyProjection_measurePreserving beta μ j).quasiMeasurePreserving
  exact ⟨hp.ae hc, fun t => hp.ae (he t)⟩

 theorem copyContinuousPosterior_compact
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) (j : Bool) :
    ∀ᵐ q ∂copies beta μ, ∀ T : ℝ≥0,
      ∃ r < (1 : ℝ), ∀ t ≤ T, |copyContinuousPosterior beta v j t q| ≤ r := by
  filter_upwards [(copyContinuousPosterior_modification hd hμ hb hcrit v j).1] with q hc
  intro T
  obtain ⟨r, hr0, hr1, hr⟩ := PosteriorInteriorLocalization.exists_uniform_radius_of_compact
    (s := Icc (0 : ℝ≥0) T) isCompact_Icc hc.continuousOn
    (fun t _ => continuousPosterior_interior beta v t (projection j q))
  exact ⟨r, hr1, fun t ht => hr t ⟨zero_le, ht⟩⟩

def copyResponseEnergy {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : ℝ :=
  infiniteGibbsResponseRow beta v (fun i => projection j q i t)

lemma copyResponseEnergy_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (copyResponseEnergy beta v j) := by
  cases j
  · exact isStronglyProgressive_infiniteGibbsResponseRow _ beta v _
      IsingConditionalCopyBounds.progressive_rightObservation
  · exact isStronglyProgressive_infiniteGibbsResponseRow _ beta v _
      IsingConditionalCopyBounds.progressive_leftObservation

 theorem copyResponseEnergy_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (j : Bool) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => copyResponseEnergy beta v j p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ)) :=
  (copy_row_energy_integrable hμ hb v j T.coe_nonneg).2.1

def commonResponseCompensator {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    ℝ≥0 → Joint d → ℝ :=
  nnrealTimePrimitive (fun t q =>
    copyResponseEnergy beta v true t q + copyResponseEnergy beta v false t q)

lemma commonResponseCompensator_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (commonResponseCompensator beta v) :=
  isStronglyProgressive_nnrealTimePrimitive
    ((copyResponseEnergy_progressive beta v true).add (copyResponseEnergy_progressive beta v false))

 theorem commonResponseCompensator_continuous
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (v : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ, Continuous (fun t => commonResponseCompensator beta v t q) := by
  apply ae_continuous_nnrealTimePrimitive_of_joint
  intro n
  have hi := (copyResponseEnergy_integrable hμ hb v true (n : ℝ≥0)).add
    (copyResponseEnergy_integrable hμ hb v false (n : ℝ≥0))
  convert hi using 1; rfl

def commonPosteriorExit {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (n : ℕ) (q : Joint d) : WithTop ℝ≥0 :=
  min (jointExit (copyContinuousPosterior beta v true) (commonResponseCompensator beta v) n q)
    (jointExit (copyContinuousPosterior beta v false) (commonResponseCompensator beta v) n q)

 theorem isLocalizingSequence_commonPosteriorExit
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    IsLocalizingSequence ContinuousCopyBrownian.joinedFiltration.rightCont
      (commonPosteriorExit beta v) (copies beta μ) := by
  have h (j : Bool) := isLocalizingSequence_jointExit_rightCont
    (copyContinuousPosterior_progressive beta v j).stronglyAdapted.adapted
    (commonResponseCompensator_progressive beta v).stronglyAdapted.adapted
    (copyContinuousPosterior_compact hd hμ hb hcrit v j)
    (commonResponseCompensator_continuous hμ hb v)
  exact (h true).min (h false)

 theorem ae_eventually_le_commonPosteriorExit
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d)
    (T : ℝ≥0) :
    ∀ᵐ q ∂copies beta μ, ∀ᶠ n in atTop,
      (T : WithTop ℝ≥0) ≤ commonPosteriorExit beta v n q := by
  filter_upwards [copyContinuousPosterior_compact hd hμ hb hcrit v true,
    copyContinuousPosterior_compact hd hμ hb hcrit v false,
    commonResponseCompensator_continuous hμ hb v] with q hl hr hA
  filter_upwards [eventually_le_jointExit (hl T) hA,
    eventually_le_jointExit (hr T) hA] with n hn hn'
  exact le_min hn hn'

end Problem367.IsingObservationFactor

end

end OAI
