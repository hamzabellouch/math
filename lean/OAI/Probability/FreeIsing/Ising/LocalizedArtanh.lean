import OAI.Probability.FreeIsing.Energy.ArtanhResponseCoefficients
import OAI.Probability.FreeIsing.Estimates.LocalizedArtanhFormula
import OAI.Probability.FreeIsing.Gibbs.CompensatedSquare
import OAI.Probability.FreeIsing.Martingales.ContinuousPosteriorMartingale

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367
open ArtanhMartingaleFormula PosteriorCompensatorStopping

def IsingJointExitArtanhData {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (beta : ℝ) (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t))
    (m : TreeVertex d → ℝ≥0 → ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ)
    (v : TreeVertex d) (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : Prop :=
  let X := plantedArrayObservation B FiniteIsingFiltering.signal
  let a := fun t p => ∑' w, infiniteGibbsCovariance beta v w (fun i => X i t p) ^ 2
  let F := arrayObservationFiltration B hmB FiniteIsingFiltering.signal
    FiniteIsingFiltering.measurable_signal
  let τ := jointExit (m v) (nnrealTimePrimitive a)
  IsLocalizingSequence F.rightCont τ P ∧
  ∀ n (T : ℝ≥0), let N := stoppedProcess (m v) (τ n)
    ∃ L, StronglyMeasurable L ∧ MemLp L 2 P ∧
      Tendsto (fun k => ∫ p,
        (BrownianGrid.uniformSum N (fun t p => firstWeight (N t p)) T k p - L p) ^ 2
        ∂P) atTop (𝓝 0) ∧
      (fun p => Real.artanh (N T p)) =ᵐ[P]
        fun p => L p + stoppedProcess
          (nnrealTimePrimitive (fun s q => m v s q *
            infiniteGibbsResponseRow beta v (fun i => X i s q))) (τ n) T p

theorem HasFreeIsingLaw.continuous_posterior_jointExit_artanh
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    {m : TreeVertex d → ℝ≥0 →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ}
    (hprog : ∀ v, IsStronglyProgressive
      (arrayObservationFiltration B hmB FiniteIsingFiltering.signal
        FiniteIsingFiltering.measurable_signal) (m v))
    (hcm : ∀ v, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Continuous (fun t => m v t p))
    (hversion : ∀ v t, m v t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (fun p => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))))
    (v : TreeVertex d) :
    IsingJointExitArtanhData beta B hmB m v (μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  let F := arrayObservationFiltration B hmB FiniteIsingFiltering.signal
    FiniteIsingFiltering.measurable_signal
  let X := plantedArrayObservation B FiniteIsingFiltering.signal
  let a := fun t p => ∑' w, infiniteGibbsCovariance beta v w (fun i => X i t p) ^ 2
  have hX (i : TreeVertex d) : IsStronglyProgressive F (X i) := by
    apply (arrayNaturalFiltration_stronglyAdapted X
      (plantedArrayObservation_measurable hmB FiniteIsingFiltering.measurable_signal) i).isStronglyProgressive_of_continuous
    intro p
    exact (hcB i (p.2 i)).add (continuous_subtype_val.mul continuous_const)
  have ha : IsStronglyProgressive F a :=
    ArtanhResponseCoefficients.isStronglyProgressive_covarianceSquareRow F beta v X hX
  have heq (r : ℝ) (hr : 0 ≤ r) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
      a r.toNNReal p = gibbsCovarianceEnergy beta v B (r, p) := by
    simp only [a, X, plantedArrayObservation, FiniteIsingFiltering.signal,
      gibbsCovarianceEnergy, Real.coe_toNNReal r hr, add_comm]
    rfl
  have hA : nnrealTimePrimitive a = gibbsCovarianceCompensator beta v B := by
    funext t p
    rw [nnrealTimePrimitive, gibbsCovarianceCompensator,
      intervalIntegral.integral_of_le t.coe_nonneg,
      intervalIntegral.integral_of_le t.coe_nonneg]
    exact setIntegral_congr_fun measurableSet_Ioc (fun r hr => heq r hr.1.le p)
  have hi (T : ℝ≥0) : Integrable (fun p : ℝ × _ => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P) := by
    have h := (hμ.infiniteGibbsCovariance_timeEnergy ν
      (fun i => (hB i).toIsPreBrownianReal) hmB hcB v T.coe_nonneg).2.2.2.1
    apply h.congr
    have hmem : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P),
        p.1 ∈ Ioc (0 : ℝ) (T : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    exact (heq p.1 hp.1.le p.2).symm
  have hM : Martingale (m v) F P :=
    (hμ.continuous_posterior_stopped_martingale hb ν hB hmB hprog hcm hversion v).1
  have hQ : Martingale (fun t p => m v t p ^ 2 - nnrealTimePrimitive a t p) F P := by
    rw [hA]
    apply (hμ.infiniteGibbsSpinMean_compensatedSquare_martingale hd hb hcrit ν
      (fun i => (hB i).toIsPreBrownianReal) hmB hcB v).congr
      (fun t => (((hprog v).stronglyAdapted t).pow 2).sub
        (stronglyAdapted_gibbsCovarianceCompensator beta v B hmB hcB t))
    intro t
    filter_upwards [hversion v t] with p hp
    change infiniteGibbsSpinMean beta v (brownianIsingObservationR B ((t : ℝ), p)) ^ 2 -
      gibbsCovarianceCompensator beta v B t p = m v t p ^ 2 - gibbsCovarianceCompensator beta v B t p
    have hobs : brownianIsingObservationR B ((t : ℝ), p) =
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) := by
      funext i
      simp only [brownianIsingObservationR, Real.toNNReal_coe]
    rw [hobs, hp]
  have hzero : ∀ᵐ p ∂P, m v 0 p = 0 := by
    have h := hμ.posterior_version_initial_zero ν (fun i => (hB i).toIsPreBrownianReal)
      (fun i => by simpa only [NNReal.coe_zero, zero_mul, zero_add] using hversion i 0)
    exact h.mono (fun p hp => (hp v).1)
  have hfield := hμ.continuous_posterior_all_time_field_bound hb ν hB hmB hcm hversion
  have hbound : ∀ᵐ p ∂P, ∀ t, |m v t p| ≤ 1 :=
    hfield.mono (fun p hp t => (abs_lt.mpr ((hp v).1 t).1).le)
  have hcompact : ∀ᵐ p ∂P, ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |m v t p| ≤ r := by
    filter_upwards [hμ.continuous_posterior_compact_localization hb ν hB hmB hcm hversion]
      with p hp
    intro T
    obtain ⟨n, hn⟩ := (hp v T).exists
    exact ⟨PosteriorInteriorLocalization.radius n,
      PosteriorInteriorLocalization.radius_lt_one n, fun t ht => (hn t ht).le⟩
  refine ⟨LocalizedArtanhFormula.isLocalizingSequence_jointExit_primitive
    (hprog v) ha (fun n => by simpa only [NNReal.coe_natCast] using hi (n : ℝ≥0)) hcompact, ?_⟩
  intro n T
  obtain ⟨L, hmL, hL2, hlim, hformula⟩ :=
    LocalizedArtanhFormula.exists_jointExit_artanh_decomposition hM hQ (hprog v) ha
      (hcm v) hzero hbound (Eventually.of_forall fun p t => tsum_nonneg (fun w => sq_nonneg _)) hi n T
  have hdrift := ArtanhResponseCoefficients.ae_all_primitive_eq_responseDrift beta v X hX
    (hprog v) (fun t => by simpa only [X, plantedArrayObservation,
      FiniteIsingFiltering.signal, add_comm] using hversion v t)
  refine ⟨L, hmL, hL2, hlim, ?_⟩
  filter_upwards [hformula, hzero, hdrift] with p hp hz hd
  simp only [hz, Real.artanh_zero, sub_zero] at hp
  rw [hp]
  congr 1
  exact hd _

end Problem367

end

end OAI
