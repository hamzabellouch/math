import OAI.Probability.FreeIsing.Brownian.ArbitraryHorizon
import OAI.Probability.FreeIsing.Ising.CanonicalClippedWeight
import OAI.Probability.FreeIsing.Ising.CanonicalDriftRegularity
import OAI.Probability.FreeIsing.Ising.CanonicalIntegralRepresentation
import OAI.Probability.FreeIsing.Ising.CanonicalResponseIntegrals
import OAI.Probability.FreeIsing.Martingales.StoppedIdentityExhaustion
import OAI.Probability.FreeIsing.Martingales.StoppedRowNormalization

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation BrownianGrid
open DominatedMartingaleRightContinuation

theorem canonical_stopped_field_eq_of_integral_limits
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {I J : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Z : ℝ≥0 → Paths d → ℝ}
    (hIp : ∀ a, IsStronglyProgressive (filtration d) (I a))
    (hIM : ∀ a, Martingale (I a) (filtration d) (observationLaw μ))
    (hJM : ∀ a, Martingale (J a) (filtration d) (observationLaw μ))
    (hZM : Martingale Z (filtration d) (observationLaw μ))
    (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
    (hJ2 : ∀ a t, MemLp (J a t) 2 (observationLaw μ))
    (hZ2 : ∀ t, MemLp (Z t) 2 (observationLaw μ))
    (hcI : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => I a t x))
    (hcJ : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J a t x))
    (hcZ : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Z t x))
    (n : ℕ) (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T))
      ((posterior_memLp beta μ (ConnectedHull.root d) T 2).toLp
        (posterior beta (ConnectedHull.root d) T)))
    (hsumJ : HasSum (fun a => (hJ2 a T).toLp (J a T)) ((hZ2 T).toLp (Z T)))
    (hIlim : ∀ a, Tendsto (fun k => ∫ x,
      (uniformSum (fun t x => innovationMap beta x a t)
        (continuousRootCovariance hb a) T k x - I a T x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0))
    (hJlim : ∀ a, Tendsto (fun k => ∫ x,
      (uniformSum (fun t x => innovationMap beta x a t)
        (continuousRootResponse hb a) T k x - J a T x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0)) :
    let τ := canonicalPosteriorExit beta (ConnectedHull.root d) n
    stoppedProcess (continuousField beta (ConnectedHull.root d)) τ T =ᵐ[observationLaw μ]
      (fun x => stoppedProcess Z τ T x +
        stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d))) τ T x) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let M := continuousPosterior beta (ConnectedHull.root d)
  let τ := canonicalPosteriorExit beta (ConnectedHull.root d) n
  let K := canonicalClippedWeight (d := d) beta n
  have hM := continuousPosterior_martingale hd hμ hb hcrit (ConnectedHull.root d)
  have hcM := (continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).1
  have hM2 (t : ℝ≥0) : MemLp (M t) 2 (observationLaw μ) :=
    MemLp.ae_eq ((continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).2 t).symm
      (posterior_memLp beta μ (ConnectedHull.root d) t 2)
  have hsumM : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hM2 T).toLp (M T)) := by
    have he := (posterior_memLp beta μ (ConnectedHull.root d) T 2).toLp_congr (hM2 T)
      ((continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).2 T).symm
    exact he ▸ hsumI
  have hτ : IsStoppingTime (filtration d).rightCont τ :=
    (canonicalPosteriorExit_localizing hd hμ hb hcrit (ConnectedHull.root d)).isStoppingTime n
  have hk : 0 ≤ 1 / (1 - PosteriorStoppingTimes.threshold n ^ 2) := by
    apply one_div_nonneg.mpr
    nlinarith [PosteriorStoppingTimes.threshold_nonneg n,
      PosteriorStoppingTimes.threshold_lt_one n]
  have hbK : ∀ᵐ x ∂observationLaw μ, ∀ t, |K t x| ≤
      1 / (1 - PosteriorStoppingTimes.threshold n ^ 2) :=
    Eventually.of_forall (fun x t => canonicalClippedWeight_bound beta n t x)
  have hK := (canonicalClippedWeight_progressive (d := d) beta n).stronglyAdapted
  have hnorm := StoppedRowNormalization.stopped_row_normalization
    (fun a => (innovationMap_isBrownianReal hμ a).toIsPreBrownianReal)
    (innovationMap_stronglyAdapted beta)
    (fun a s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
      (B := fun a t x => innovationMap beta x a t) (F := filtration d)
      (innovationMap_increment_indep_filtration hμ s t hst) a)
    (fun a => (innovationMap_isBrownianReal hμ a).cont)
    (fun a => (continuousRootCovariance_progressive hb a).stronglyAdapted)
    (fun a => (continuousRootResponse_progressive hb a).stronglyAdapted) hK
    (continuousRootCovariance_continuous_ae hd hμ hb hcrit)
    (canonicalClippedWeight_continuous_ae hd hμ hb hcrit n)
    (c := fun _ => 1) (r := fun _ => 1) (fun _ => by norm_num) hk
    (fun a => Eventually.of_forall (fun x t => continuousRootCovariance_abs_le_one hb a t x))
    (fun a => Eventually.of_forall (fun x t => continuousRootResponse_abs_le_one hb a t x)) hbK
    hIM hJM hM hZM hI2 hJ2 hM2 hZ2 hcI hcJ hcM hcZ hIp
    (continuousPosterior_progressive beta (ConnectedHull.root d)) T hsumM hsumJ hIlim hJlim hτ
    (fun a => (canonicalClippedWeight_mul_covariance_before_exit hd hμ hb hcrit n).mono
      (fun x hx t ht => hx t ht a))
  obtain ⟨L, hmL, hL2, hlimL, hfield⟩ :=
    canonical_artanh_decomposition hd hμ hb hcrit (ConnectedHull.root d) n T
  have hlimL' : Tendsto (fun k => ∫ x,
      (uniformSum (stoppedProcess M τ) K T k x - L x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0) := by
    apply hlimL.congr
    intro k
    apply integral_congr_ae
    filter_upwards [canonicalClippedWeight_uniformSum_eq hd hμ hb hcrit n T k] with x hx
    rw [hx]
  have hMs2 (t : ℝ≥0) := StoppedMartingaleL2.memLp_stoppedProcess_two
    (martingale_rightCont_of_ae_continuous_memLp_two hM hM2 hcM) hM2 hcM hτ t
  have hZs2 := StoppedMartingaleL2.memLp_stoppedProcess_two
    (martingale_rightCont_of_ae_continuous_memLp_two hZM hZ2 hcZ) hZ2 hcZ hτ T
  have heq := ae_eq_of_mean_square_limits
    (fun k => BrownianContinuousAssociativity.uniformSum_memLp hMs2 hK hbK T k)
    hL2 hZs2 hlimL' hnorm
  filter_upwards [hfield, heq] with x hx he
  exact hx.trans (congrArg (fun z => z +
    stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d))) τ T x) he)

theorem canonical_field_eq_normalized_integral
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {J : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Z : ℝ≥0 → Paths d → ℝ}
    (hJM : ∀ a, Martingale (J a) (filtration d) (observationLaw μ))
    (hZM : Martingale Z (filtration d) (observationLaw μ))
    (hJ2 : ∀ a t, MemLp (J a t) 2 (observationLaw μ))
    (hZ2 : ∀ t, MemLp (Z t) 2 (observationLaw μ))
    (hcJ : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J a t x))
    (hcZ : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Z t x))
    (hsumJ : ∀ t, HasSum (fun a => (hJ2 a t).toLp (J a t)) ((hZ2 t).toLp (Z t)))
    (hJlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun k => ∫ x,
        (BrownianIntegralProcess.stoppedUniformSum
          (fun s x => innovationMap beta x a s) (continuousRootResponse hb a)
          N k t x - J a t x) ^ 2 ∂observationLaw μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂observationLaw μ, ∀ t,
      continuousField beta (ConnectedHull.root d) t x = Z t x +
        nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d)) t x := by
  obtain ⟨I, hI2, hIp, hIM, hcI, hI0, hImean, hIenergy, hIlim, hsumI⟩ :=
    exists_canonical_root_covariance_integral_representation hd hμ hb hcrit
  have hind (a : TreeVertex d) (s t : ℝ≥0) (hst : s ≤ t) :=
    BrownianArrayFiltration.coordinate_increment_indep_past
      (B := fun a t x => innovationMap beta x a t) (F := filtration d)
      (innovationMap_increment_indep_filtration hμ s t hst) a
  have hIuniform (a : TreeVertex d) (T : ℝ≥0) :=
    BrownianArbitraryHorizon.uniformSum_tendsto_of_integer_stopped_limits
      (innovationMap_isBrownianReal hμ a).toIsPreBrownianReal
      (innovationMap_stronglyAdapted beta a) (hind a)
      (innovationMap_isBrownianReal hμ a).cont
      (continuousRootCovariance_progressive hb a).stronglyAdapted
      (continuousRootCovariance_continuous_ae hd hμ hb hcrit a)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (Eventually.of_forall (fun x t => continuousRootCovariance_abs_le_one hb a t x))
      (hIM a) (hI2 a) (hcI a) (hIlim a) T
  have hJuniform (a : TreeVertex d) (T : ℝ≥0) :=
    BrownianArbitraryHorizon.uniformSum_tendsto_of_integer_stopped_limits
      (innovationMap_isBrownianReal hμ a).toIsPreBrownianReal
      (innovationMap_stronglyAdapted beta a) (hind a)
      (innovationMap_isBrownianReal hμ a).cont
      (continuousRootResponse_progressive hb a).stronglyAdapted
      (continuousRootResponse_continuous_ae hd hμ hb hcrit a)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (Eventually.of_forall (fun x t => continuousRootResponse_abs_le_one hb a t x))
      (hJM a) (hJ2 a) (hcJ a) (hJlim a) T
  have hstop (n : ℕ) (T : ℝ≥0) :=
    canonical_stopped_field_eq_of_integral_limits hd hμ hb hcrit
      (fun a => (hIp a).isStronglyProgressive) hIM hJM hZM hI2 hJ2 hZ2 hcI hcJ hcZ
      n T (hsumI T) (hsumJ T) (fun a => hIuniform a T) (fun a => hJuniform a T)
  exact StoppedIdentityExhaustion.ae_all_add_of_localizing_stopped_add
    (canonicalPosteriorExit_localizing hd hμ hb hcrit (ConnectedHull.root d))
    (continuousField_modification hd hμ hb hcrit (ConnectedHull.root d)).1
    hcZ (canonicalResponseDrift_primitive_continuous hμ hb (ConnectedHull.root d)) hstop

end Problem367.IsingObservationFactor

end

end OAI
