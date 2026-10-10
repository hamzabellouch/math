import OAI.Probability.FreeIsing.Factors.ContinuousRecovery
import OAI.Probability.FreeIsing.Ising.CanonicalDriftRegularity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation PosteriorCompensatorStopping ArtanhMartingaleFormula

theorem canonical_artanh_uniformSum_memLp
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d)
    (n : ℕ) (T : ℝ≥0) (k : ℕ) :
    let N := stoppedProcess (continuousPosterior beta v) (canonicalPosteriorExit beta v n)
    MemLp (BrownianGrid.uniformSum N (fun t x => firstWeight (N t x)) T k) 2
      (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let F := (filtration d).rightCont
  let N := stoppedProcess (continuousPosterior beta v) (canonicalPosteriorExit beta v n)
  have hprog : IsStronglyProgressive F N :=
    (DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
      (filtration d).le_rightCont (continuousPosterior_progressive beta v)).stoppedProcess
        ((canonicalPosteriorExit_localizing hd hμ hb hcrit v).isStoppingTime n)
  have hbound : ∀ᵐ x ∂observationLaw μ, ∀ t, |N t x| ≤ PosteriorStoppingTimes.threshold n := by
    filter_upwards [(continuousPosterior_modification hd hμ hb hcrit v).1,
      continuousPosterior_initial_zero hd hμ hb hcrit v] with x hc hz
    exact abs_stopped_posterior_le hc hz n
  have hN2 (t : ℝ≥0) : MemLp (N t) 2 (observationLaw μ) := by
    apply MemLp.of_bound ((hprog.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
      (PosteriorStoppingTimes.threshold n)
    simpa only [Real.norm_eq_abs] using hbound.mono (fun x hx => hx t)
  apply MartingaleUniformIntegral.uniformSum_memLp hN2
    (fun t => stronglyMeasurable_firstWeight (hprog.stronglyAdapted t))
    (K := 1 / (1 - PosteriorStoppingTimes.threshold n ^ 2)) _ T k
  intro t
  exact hbound.mono (fun x hx => firstWeight_bound
    (PosteriorStoppingTimes.threshold_nonneg n) (PosteriorStoppingTimes.threshold_lt_one n) (hx t))

theorem canonical_artanh_eq_of_meanSquare_limit
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d)
    (n : ℕ) (T : ℝ≥0) {J : Paths d → ℝ}
    (hJ : MemLp J 2 (observationLaw μ))
    (hlim : let N := stoppedProcess (continuousPosterior beta v) (canonicalPosteriorExit beta v n)
      Tendsto (fun k => ∫ x,
        (BrownianGrid.uniformSum N (fun t x => firstWeight (N t x)) T k x - J x) ^ 2
          ∂observationLaw μ) atTop (𝓝 0)) :
    stoppedProcess (continuousField beta v) (canonicalPosteriorExit beta v n) T =ᵐ[observationLaw μ]
      fun x => J x + stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta v))
        (canonicalPosteriorExit beta v n) T x := by
  obtain ⟨L, _, hL, hLlim, hfield⟩ := canonical_artanh_decomposition hd hμ hb hcrit v n T
  have heq := BrownianGrid.ae_eq_of_mean_square_limits
    (canonical_artanh_uniformSum_memLp hd hμ hb hcrit v n T) hL hJ hLlim hlim
  filter_upwards [hfield, heq] with x hx hLJ
  exact hx.trans (congrArg (fun z => z + stoppedProcess
    (nnrealTimePrimitive (canonicalResponseDrift beta v)) (canonicalPosteriorExit beta v n) T x) hLJ)

theorem canonical_artanh_eq_all_of_meanSquare_limits
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d)
    (n : ℕ) {J : ℝ≥0 → Paths d → ℝ}
    (hJ : ∀ T, MemLp (J T) 2 (observationLaw μ))
    (hcJ : ∀ᵐ x ∂observationLaw μ, Continuous (fun T => J T x))
    (hlim : ∀ T, let N := stoppedProcess (continuousPosterior beta v) (canonicalPosteriorExit beta v n)
      Tendsto (fun k => ∫ x,
        (BrownianGrid.uniformSum N (fun t x => firstWeight (N t x)) T k x - J T x) ^ 2
          ∂observationLaw μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂observationLaw μ, ∀ T,
      stoppedProcess (continuousField beta v) (canonicalPosteriorExit beta v n) T x =
        J T x + stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta v))
          (canonicalPosteriorExit beta v n) T x := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hcA : ∀ᵐ x ∂observationLaw μ,
      Continuous (fun T => nnrealTimePrimitive (canonicalResponseDrift beta v) T x) :=
    canonicalResponseDrift_primitive_continuous hμ hb v
  have hleft := (continuousField_modification hd hμ hb hcrit v).1.mono
    (fun x hx => StoppedTimePrimitive.continuous_stoppedProcess hx (canonicalPosteriorExit beta v n))
  have hright := (hcJ.and hcA).mono (fun x hx => hx.1.add
    (StoppedTimePrimitive.continuous_stoppedProcess hx.2 (canonicalPosteriorExit beta v n)))
  have h := ae_eq_of_continuous_of_evaluation_ae_eq hleft hright
    (fun T => canonical_artanh_eq_of_meanSquare_limit hd hμ hb hcrit v n T (hJ T) (hlim T))
  exact h.mono (fun x hx T => congrFun hx T)

end Problem367.IsingObservationFactor

end

end OAI
