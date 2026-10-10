import OAI.Probability.FreeIsing.Energy.DiscrepancyRowEnergy
import OAI.Probability.FreeIsing.Energy.NormalizedResponseLimit
import OAI.Probability.FreeIsing.Posterior.InfinitePosteriorField

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem integrable_sq_and_integral_le_of_tendsto_ae
    (μ : Measure Ω) {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {K : ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hY : AEStronglyMeasurable Y μ) (hK : 0 ≤ K)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hbound : ∀ᶠ n in atTop, Integrable (fun ω => (X n ω) ^ 2) μ ∧
      (∫ ω, (X n ω) ^ 2 ∂μ) ≤ K) :
    Integrable (fun ω => (Y ω) ^ 2) μ ∧ (∫ ω, (Y ω) ^ 2 ∂μ) ≤ K := by
  have hfatou : (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ) ≤ ENNReal.ofReal K := by
    calc
      (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ) =
          ∫⁻ ω, liminf (fun n => ENNReal.ofReal ((X n ω) ^ 2)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (hω.pow 2)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((X n ω) ^ 2) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => ((hX n).pow 2).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal K := by
        apply liminf_le_of_frequently_le'
        apply Filter.Eventually.frequently
        filter_upwards [hbound] with n hn
        rw [← ofReal_integral_eq_lintegral_ofReal hn.1
          (Filter.Eventually.of_forall (fun ω => sq_nonneg (X n ω)))]
        exact ENNReal.ofReal_le_ofReal hn.2
  refine ⟨⟨hY.pow 2, ?_⟩, ?_⟩
  · apply (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω)))).mpr
    exact hfatou.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω))) (hY.pow 2)]
    exact ENNReal.toReal_le_of_le_ofReal hK hfatou

theorem posteriorResponse_integrable_sq_of_uniform_bound
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (f g : Ω → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hinterior : ∀ᵐ ω ∂μ, μ[f | ⨆ n, F n] ω ∈ Set.Ioo (-1 : ℝ) 1)
    (hbound : ∀ᶠ n in atTop,
      Integrable (fun ω => (posteriorResponse μ (F n) f g ω) ^ 2) μ ∧
      (∫ ω, (posteriorResponse μ (F n) f g ω) ^ 2 ∂μ) ≤ K) :
    Integrable (fun ω => (posteriorResponse μ (⨆ n, F n) f g ω) ^ 2) μ ∧
      (∫ ω, (posteriorResponse μ (⨆ n, F n) f g ω) ^ 2 ∂μ) ≤ K := by
  exact integrable_sq_and_integral_le_of_tendsto_ae μ
    (fun n => ((stronglyMeasurable_posteriorResponse μ (F n) f g).mono
      (F.le n)).aestronglyMeasurable)
    (((stronglyMeasurable_posteriorResponse μ (⨆ n, F n) f g).mono
      (iSup_le fun n => F.le n)).aestronglyMeasurable)
    hK (tendsto_ae_posteriorResponse μ F f g hinterior) hbound

theorem posteriorResponse_row_energy_of_uniform_bounds
    {ι : Type*} [Countable ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (f : Ω → ℝ) (g : ι → Ω → ℝ) (K : ι → ℝ)
    (hK : ∀ i, 0 ≤ K i) (hKs : Summable K)
    (hinterior : ∀ᵐ ω ∂μ, μ[f | ⨆ n, F n] ω ∈ Set.Ioo (-1 : ℝ) 1)
    (hbound : ∀ i, ∀ᶠ n in atTop,
      Integrable (fun ω => (posteriorResponse μ (F n) f (g i) ω) ^ 2) μ ∧
      (∫ ω, (posteriorResponse μ (F n) f (g i) ω) ^ 2 ∂μ) ≤ K i) :
    (∀ᵐ ω ∂μ, Summable (fun i => (posteriorResponse μ (⨆ n, F n) f (g i) ω) ^ 2)) ∧
      Integrable (fun ω => ∑' i, (posteriorResponse μ (⨆ n, F n) f (g i) ω) ^ 2) μ ∧
      (∫ ω, (∑' i, (posteriorResponse μ (⨆ n, F n) f (g i) ω) ^ 2) ∂μ) ≤
        ∑' i, K i := by
  have hb (i : ι) := posteriorResponse_integrable_sq_of_uniform_bound μ F f (g i)
    (hK i) hinterior (hbound i)
  have hs : Summable (fun i =>
      ∫ ω, (posteriorResponse μ (⨆ n, F n) f (g i) ω) ^ 2 ∂μ) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun ω => sq_nonneg _))
      (fun i => (hb i).2) hKs
  obtain ⟨hae, hint⟩ := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun i => (hb i).1) hs
  refine ⟨hae, hint, ?_⟩
  have heq := DiscrepancyEnergy.hasSum_integral_sq_row
    (fun i => ((stronglyMeasurable_posteriorResponse μ (⨆ n, F n) f (g i)).mono
      (iSup_le fun n => F.le n)).aestronglyMeasurable) hae hint
  rw [← heq.tsum_eq]
  exact hs.tsum_le_tsum (fun i => (hb i).2) hKs

section Gaussian

open PlantedSymmetry

def gaussianPosteriorResponse {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v w : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
  posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (observationSigma (TreeVertex d) t)
    (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w))

theorem HasFreeIsingLaw.finiteObservation_posteriorResponse
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0)
    (v w : D) :
    posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun p => spinSign (p.1 v.1)) (fun p => spinSign (p.1 w.1)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p =>
        let M := fun q => FinitePosterior.fieldMean (finiteIsingEnergy beta D)
          (fun (eta : D → IsingSpin) u => spinSign (eta u)) q (finiteObservation D t p)
        (M (fun eta => spinSign (eta v) * spinSign (eta w)) -
          M (fun eta => spinSign (eta v)) * M (fun eta => spinSign (eta w))) /
          (1 - (M (fun eta => spinSign (eta v))) ^ 2) := by
  filter_upwards [hμ.finiteObservation_condExp D hD t
      (fun eta => spinSign (eta v) * spinSign (eta w)),
    hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v)),
    hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta w))]
    with p hpair hv hw
  dsimp only [posteriorResponse, posteriorCovariance]
  simp only [Finset.restrict] at hpair hv hw
  rw [hpair, hv, hw]

theorem HasFreeIsingLaw.gaussian_posteriorResponse_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p) atTop
        (𝓝 (gaussianPosteriorResponse μ t v w p)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hi := (hμ.gaussian_posterior_field_bound hbeta t v).mono (fun _ h => h.1)
  have hi' : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) | ⨆ n, finiteObservationFiltration D hD t n] p ∈
        Set.Ioo (-1 : ℝ) 1 := by
    rw [finiteObservationFiltration_iSup D hD hex t]
    exact hi
  have h := tendsto_ae_posteriorResponse
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) hi'
  rw [finiteObservationFiltration_iSup D hD hex t] at h
  exact h

theorem HasFreeIsingLaw.gaussian_posteriorResponse_integrable_sq
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) (v w : TreeVertex d)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᶠ n in atTop,
      Integrable (fun p => (posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p) ^ 2)
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
      (∫ p, (posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤ K) :
    Integrable (fun p => (gaussianPosteriorResponse μ t v w p) ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
      (∫ p, (gaussianPosteriorResponse μ t v w p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤ K := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply integrable_sq_and_integral_le_of_tendsto_ae
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (fun n => ((stronglyMeasurable_posteriorResponse _ _ _ _).mono
      (measurable_finiteObservation (D n) t).comap_le).aestronglyMeasurable)
    (((stronglyMeasurable_posteriorResponse _ _ _ _).mono
      (observationSigma_le (TreeVertex d) t)).aestronglyMeasurable)
    hK (hμ.gaussian_posteriorResponse_tendsto_ae hbeta D hD hex t v w) hbound

theorem HasFreeIsingLaw.gaussian_posteriorResponse_meanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) (v w : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      (posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p -
        gaussianPosteriorResponse μ t v w p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hi := (hμ.gaussian_posterior_field_bound hbeta t v).mono (fun _ h => h.1)
  have hi' : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) | ⨆ n, finiteObservationFiltration D hD t n] p ∈
        Set.Ioo (-1 : ℝ) 1 := by
    rw [finiteObservationFiltration_iSup D hD hex t]
    exact hi
  have hb : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      spinSign (p.1 v) = -1 ∨ spinSign (p.1 v) = 1 :=
    Filter.Eventually.of_forall (fun p => by cases p.1 v <;> simp [spinSign])
  have hgb : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      |spinSign (p.1 w)| ≤ 1 :=
    Filter.Eventually.of_forall (fun p => by cases p.1 w <;> norm_num [spinSign])
  have h := tendsto_integral_sq_sub_posteriorResponse
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (integrable_plantedSpin _ v) (integrable_plantedSpin _ w) hb hgb hi'
  rw [finiteObservationFiltration_iSup D hD hex t] at h
  exact h

end Gaussian

end Problem367

end

end OAI
