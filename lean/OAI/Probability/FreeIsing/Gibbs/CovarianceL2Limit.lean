import OAI.Probability.FreeIsing.Energy.ProgressiveIsingCovariance
import OAI.Probability.FreeIsing.Posterior.DerivativeBounds

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367

open PlantedSymmetry

local instance covarianceL2LimitNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

def finiteGibbsCovarianceOn {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (v w : D) (y : D → ℝ) : ℝ :=
  FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v) * spinSign (eta w)) y -
  FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v)) y *
  FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta w)) y

lemma continuous_finiteGibbsCovarianceOn {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v w : D) :
    Continuous (finiteGibbsCovarianceOn beta D v w) := by
  exact (FinitePosterior.continuous_fieldMean _ _ _).sub
    ((FinitePosterior.continuous_fieldMean _ _ _).mul
      (FinitePosterior.continuous_fieldMean _ _ _))

lemma finiteGibbsCovarianceOn_abs_le_two {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v w : D) (y : D → ℝ) :
    |finiteGibbsCovarianceOn beta D v w y| ≤ 2 := by
  have hv := FinitePosterior.abs_fieldMean_le (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v)) y 1
    (fun eta => show |spinSign (eta v)| ≤ 1 by cases eta v <;> norm_num [spinSign])
  have hw := FinitePosterior.abs_fieldMean_le (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta w)) y 1
    (fun eta => show |spinSign (eta w)| ≤ 1 by cases eta w <;> norm_num [spinSign])
  have hp := FinitePosterior.abs_fieldMean_le (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta v) * spinSign (eta w)) y 1
    (fun eta => show |spinSign (eta v) * spinSign (eta w)| ≤ 1 by
      cases eta v <;> cases eta w <;> norm_num [spinSign])
  have hprod : |FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) u => spinSign (eta u))
      (fun eta => spinSign (eta v)) y *
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) u => spinSign (eta u))
      (fun eta => spinSign (eta w)) y| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul hv hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  exact (abs_sub _ _).trans (by linarith)

def finiteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ)
    (y : TreeVertex d → ℝ) : ℝ := by
  classical
  exact if hw : w ∈ connectedExhaustion v n then
    finiteGibbsCovarianceOn beta (connectedExhaustion v n)
      ⟨v, mem_connectedExhaustion v n⟩ ⟨w, hw⟩ ((connectedExhaustion v n).restrict y)
    else 0

lemma continuous_finiteGibbsCovariance {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) : Continuous (finiteGibbsCovariance beta v w n) := by
  classical
  unfold finiteGibbsCovariance
  split_ifs with hw
  · exact (continuous_finiteGibbsCovarianceOn _ _ _ _).comp
      (continuous_pi fun u => continuous_apply u.1)
  · exact continuous_const

lemma finiteGibbsCovariance_abs_le_two {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) (y : TreeVertex d → ℝ) :
    |finiteGibbsCovariance beta v w n y| ≤ 2 := by
  classical
  unfold finiteGibbsCovariance
  split_ifs with hw
  · exact finiteGibbsCovarianceOn_abs_le_two _ _ _ _ _
  · norm_num

theorem HasFreeIsingLaw.finiteGibbsCovarianceOn_eq_posterior
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v w : D) (t : ℝ≥0) :
    (fun p => finiteGibbsCovarianceOn beta D v w (finiteObservation D t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation D t) inferInstance)
        (fun p => spinSign (p.1 v.1)) (fun p => spinSign (p.1 w.1)) := by
  filter_upwards [hμ.finiteObservation_condExp D hD t
      (fun eta => spinSign (eta v) * spinSign (eta w)),
    hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v)),
    hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta w))]
      with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp.symm
    (congrArg₂ (· * ·) hv.symm hw.symm)

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteGibbsCovariance beta v w n (observation t p)) atTop
        (𝓝 (infiniteGibbsCovariance beta v w (observation t p))) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let F := finiteObservationFiltration (connectedExhaustion v)
    (connectedExhaustion_monotone v) t
  have hlim := tendsto_ae_posteriorCovariance
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) F
    (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w))
  have hsup : (⨆ n, F n) = observationSigma (TreeVertex d) t :=
    finiteObservationFiltration_iSup (connectedExhaustion v)
      (connectedExhaustion_monotone v)
      (fun u => (eventually_mem_connectedExhaustion v u).exists) t
  rw [hsup] at hlim
  have hfinite (n : ℕ) : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      w ∈ connectedExhaustion v n →
      finiteGibbsCovariance beta v w n (observation t p) =
        posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (F n)
          (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p := by
    by_cases hw : w ∈ connectedExhaustion v n
    · filter_upwards [hμ.finiteGibbsCovarianceOn_eq_posterior
        (connectedExhaustion v n) (connectedExhaustion_connected v n)
        ⟨v, mem_connectedExhaustion v n⟩ ⟨w, hw⟩ t] with p hp
      intro _
      simpa only [finiteGibbsCovariance, dite_eq_left hw, F,
        finiteObservationFiltration, finiteObservation] using hp
    · exact Eventually.of_forall fun _ h => (hw h).elim
  filter_upwards [hlim, ae_all_iff.mpr hfinite,
    hμ.infiniteGibbsCovariance_eq_posterior t v w] with p hp hfinite hinf
  rw [← hinf] at hp
  apply hp.congr'
  filter_upwards [eventually_mem_connectedExhaustion v w] with n hn
  exact (hfinite n hn).symm

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_meanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      (finiteGibbsCovariance beta v w n (observation t p) -
        infiniteGibbsCovariance beta v w (observation t p)) ^ 2
          ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply tendsto_integral_sq_sub_of_bounded_ae _
    (fun n => ((continuous_finiteGibbsCovariance beta v w n).measurable.comp
      (measurable_observation t)).aestronglyMeasurable)
    (((measurable_infiniteGibbsCovariance beta v w).comp
      (measurable_observation t)).aestronglyMeasurable) (by norm_num : (0 : ℝ) ≤ 2)
  · exact fun n => Eventually.of_forall fun p => finiteGibbsCovariance_abs_le_two _ _ _ _ _
  · exact Eventually.of_forall fun p => infiniteGibbsCovariance_abs_le_two _ _ _ _
  · exact hμ.finiteGibbsCovariance_tendsto_ae t v w

theorem HasFreeIsingLaw.finiteGibbsCovariance_brownian_tendsto_ae
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Tendsto (fun n => finiteGibbsCovariance beta v w n
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) atTop
        (𝓝 (infiniteGibbsCovariance beta v w
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  exact hT.quasiMeasurePreserving.ae (hμ.finiteGibbsCovariance_tendsto_ae t v w)

theorem HasFreeIsingLaw.finiteGibbsCovariance_brownian_tendsto_meanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      (finiteGibbsCovariance beta v w n
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) -
        infiniteGibbsCovariance beta v w
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) ^ 2
            ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hX : Measurable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
        ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))
  apply tendsto_integral_sq_sub_of_bounded_ae _
    (fun n => ((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).aestronglyMeasurable)
    (((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)
    (by norm_num : (0 : ℝ) ≤ 2)
  · exact fun n => Eventually.of_forall fun p => finiteGibbsCovariance_abs_le_two _ _ _ _ _
  · exact Eventually.of_forall fun p => infiniteGibbsCovariance_abs_le_two _ _ _ _
  · exact hμ.finiteGibbsCovariance_brownian_tendsto_ae ν hB hmB t v w

lemma measurable_brownian_ising_observation_uncurry
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    Measurable (fun p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)) := by
  apply Measurable.of_eval
  intro i
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))
  · intro p
    exact (continuous_subtype_val.mul continuous_const).add (hcB i (p.2 i))
  · intro t
    exact (measurable_const.mul ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
        ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))

theorem HasFreeIsingLaw.finiteGibbsCovariance_brownian_tendsto_timeMeanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ] (v w : TreeVertex d) :
    Tendsto (fun n => ∫ p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
      (finiteGibbsCovariance beta v w n
          (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)) -
        infiniteGibbsCovariance beta v w
          (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i))) ^ 2
            ∂τ.prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hX := measurable_brownian_ising_observation_uncurry hmB hcB
  apply tendsto_integral_prod_sq_sub_of_bounded_ae τ (μ.prod (Measure.infinitePi ν))
    (fun n => (continuous_finiteGibbsCovariance beta v w n).measurable.comp hX)
    ((measurable_infiniteGibbsCovariance beta v w).comp hX)
    (by norm_num : (0 : ℝ) ≤ 2)
  · exact fun n => Eventually.of_forall fun t => Eventually.of_forall fun p =>
      finiteGibbsCovariance_abs_le_two _ _ _ _ _
  · exact Eventually.of_forall fun t => Eventually.of_forall fun p =>
      infiniteGibbsCovariance_abs_le_two _ _ _ _
  · exact Eventually.of_forall fun t =>
      hμ.finiteGibbsCovariance_brownian_tendsto_ae ν hB hmB t v w

end Problem367

end

end OAI
