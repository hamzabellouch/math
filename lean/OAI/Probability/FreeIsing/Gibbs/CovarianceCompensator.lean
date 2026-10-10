import OAI.Probability.FreeIsing.Energy.RowEnergyL1
import OAI.Probability.FreeIsing.Estimates.CompensatedSquareLimit
import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitive
import OAI.Probability.FreeIsing.Gibbs.CovarianceCriticalRowConvergence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367

def gibbsCovarianceEnergy {d : ℕ} {Ω : Type*} (beta : ℝ) (v : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : ℝ :=
  ∑' w, infiniteGibbsCovariance beta v w (brownianIsingObservationR B p) ^ 2

def finiteGibbsCovarianceEnergy {d : ℕ} {Ω : Type*} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : ℝ :=
  ∑' w, finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2

def gibbsCovarianceCompensator {d : ℕ} {Ω : Type*} (beta : ℝ)
    (v : TreeVertex d) (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), gibbsCovarianceEnergy beta v B (s, p)

def finiteGibbsCovarianceCompensator {d : ℕ} {Ω : Type*} (beta : ℝ)
    (v : TreeVertex d) (n : ℕ) (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), finiteGibbsCovarianceEnergy beta v n B (s, p)

lemma finiteGibbsCovarianceEnergy_eq_sum {d : ℕ} {Ω : Type*}
    (beta : ℝ) (v : TreeVertex d) (n : ℕ) (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
    finiteGibbsCovarianceEnergy beta v n B p =
      ∑ w ∈ connectedExhaustion v n,
        finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2 := by
  classical
  apply tsum_eq_sum
  intro w hw
  simp only [finiteGibbsCovariance, dite_eq_right hw, zero_pow (by decide : 2 ≠ 0)]

lemma summable_integral_finiteGibbsCovariance_sq
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (P : Measure (ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)))) :
    Summable (fun w => ∫ p,
      finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2 ∂P) := by
  classical
  apply summable_of_ne_finset_zero (s := connectedExhaustion v n)
  intro w hw
  simp only [finiteGibbsCovariance, dite_eq_right hw, zero_pow (by decide : 2 ≠ 0), integral_zero]

lemma integrable_finiteGibbsCovarianceEnergy
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (finiteGibbsCovarianceEnergy beta v n B)
      (τ.prod (μ.prod (Measure.infinitePi ν))) := by
  change Integrable (fun p => finiteGibbsCovarianceEnergy beta v n B p) _
  simp_rw [finiteGibbsCovarianceEnergy_eq_sum]
  exact integrable_finsetSum _ (fun w _ => integrable_finiteGibbsCovariance_sq
    beta v w n (measurable_brownianIsingObservationR hmB hcB))

lemma HasFreeIsingLaw.integrable_gibbsCovarianceCompensator
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (t : ℝ≥0) :
    Integrable (gibbsCovarianceCompensator beta v B t) (μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hi := (hμ.infiniteGibbsCovariance_timeEnergy ν hB hmB hcB v t.coe_nonneg).2.2.2.1
  change Integrable (fun p => ∫ s in (0 : ℝ)..(t : ℝ),
    ∑' w, infiniteGibbsCovariance beta v w (brownianIsingObservationR B (s, p)) ^ 2) _
  simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using hi.integral_prod_right

lemma integrable_finiteGibbsCovarianceCompensator
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (t : ℝ≥0) :
    Integrable (finiteGibbsCovarianceCompensator beta v n B t)
      (μ.prod (Measure.infinitePi ν)) := by
  have hi := integrable_finiteGibbsCovarianceEnergy beta v n μ ν hmB hcB
    (volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
  change Integrable (fun p => ∫ s in (0 : ℝ)..(t : ℝ),
    finiteGibbsCovarianceEnergy beta v n B (s, p)) _
  simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using hi.integral_prod_right

theorem stronglyAdapted_gibbsCovarianceCompensator
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (beta : ℝ) (v : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    StronglyAdapted
      (arrayObservationFiltration B hmB
        (fun (sigma : TreeVertex d → IsingSpin) i => spinSign (sigma i)) measurable_spinSign_array)
      (gibbsCovarianceCompensator beta v B) := by
  let F := arrayObservationFiltration B hmB
    (fun (sigma : TreeVertex d → IsingSpin) i => spinSign (sigma i)) measurable_spinSign_array
  let X := plantedArrayObservation B (fun (sigma : TreeVertex d → IsingSpin) i => spinSign (sigma i))
  have hX (i : TreeVertex d) : IsStronglyProgressive F (X i) := by
    apply (arrayNaturalFiltration_stronglyAdapted X
      (plantedArrayObservation_measurable hmB measurable_spinSign_array) i).isStronglyProgressive_of_continuous
    intro p
    exact (hcB i (p.2 i)).add (continuous_subtype_val.mul continuous_const)
  let E := fun t p => ∑' w, infiniteGibbsCovariance beta v w (fun i => X i t p) ^ 2
  have hE : IsStronglyProgressive F E := by
    intro t
    have hC (w : TreeVertex d) := isStronglyProgressive_infiniteGibbsCovariance F beta v w X hX t
    let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) := F t
    exact StronglyMeasurable.tsum (fun w => (hC w).pow 2)
  have ha := stronglyAdapted_nnrealTimePrimitive hE
  have heq : gibbsCovarianceCompensator beta v B = nnrealTimePrimitive E := by
    funext t p
    rw [gibbsCovarianceCompensator, nnrealTimePrimitive,
      intervalIntegral.integral_of_le t.coe_nonneg,
      intervalIntegral.integral_of_le t.coe_nonneg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only [gibbsCovarianceEnergy, E, X, brownianIsingObservationR, plantedArrayObservation]
    simp only [Real.coe_toNNReal r hr.1.le, add_comm]
    rfl
  rw [heq]
  exact ha

private theorem covarianceEnergy_tendsto_L1_of_row
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T)
    (hrow : Tendsto (fun n => ∑' w, ∫ p,
      (finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) -
        infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)) ^ 2
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν)))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,
      |finiteGibbsCovarianceEnergy beta v n B p - gibbsCovarianceEnergy beta v B p|
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν)))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hX := measurable_brownianIsingObservationR hmB hcB
  apply RowEnergyL1.tendsto_integral_abs_tsum_sq_sub
    (fun n w => (memLp_two_iff_integrable_sq
      (((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).aestronglyMeasurable)).2
      (integrable_finiteGibbsCovariance_sq beta v w n hX))
    (fun w => (memLp_two_iff_integrable_sq
      (((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)).2
      (integrable_infiniteGibbsCovariance_sq beta v w hX))
    (fun n => summable_integral_finiteGibbsCovariance_sq beta v n B _)
    (hμ.infiniteGibbsCovariance_timeEnergy ν hB hmB hcB v hT).1 hrow

private theorem covarianceCompensator_tendsto_L1_of_energy
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (t : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ p,
      |finiteGibbsCovarianceEnergy beta v n B p - gibbsCovarianceEnergy beta v B p|
      ∂(volume.restrict (Ioc (0 : ℝ) (t : ℝ))).prod (μ.prod (Measure.infinitePi ν)))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (finiteGibbsCovarianceCompensator beta v n B t - gibbsCovarianceCompensator beta v B t)
      1 (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hE n := integrable_finiteGibbsCovarianceEnergy beta v n μ ν hmB hcB
    (volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
  have hF := (hμ.infiniteGibbsCovariance_timeEnergy ν hB hmB hcB v t.coe_nonneg).2.2.2.1
  have hprim : Tendsto (fun n => ∫ p,
      |finiteGibbsCovarianceCompensator beta v n B t p - gibbsCovarianceCompensator beta v B t p|
      ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (fun p => abs_nonneg _)) _ hlim
    intro n
    exact RowEnergyL1.integral_abs_timePrimitive_sub_le ⟨t.coe_nonneg, le_rfl⟩ (hE n) hF
  have heq n : eLpNorm
      (finiteGibbsCovarianceCompensator beta v n B t - gibbsCovarianceCompensator beta v B t)
      1 (μ.prod (Measure.infinitePi ν)) = ENNReal.ofReal (∫ p,
      |finiteGibbsCovarianceCompensator beta v n B t p - gibbsCovarianceCompensator beta v B t p|
        ∂μ.prod (Measure.infinitePi ν)) := by
    have hint := (integrable_finiteGibbsCovarianceCompensator beta v n μ ν hmB hcB t).sub
      (hμ.integrable_gibbsCovarianceCompensator ν hB hmB hcB v t)
    rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hint]
    rfl
  simp_rw [heq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hprim

theorem HasFreeIsingLaw.finiteGibbsCovarianceEnergy_tendsto_L1
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => ∫ p,
      |finiteGibbsCovarianceEnergy beta v n B p - gibbsCovarianceEnergy beta v B p|
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν)))
      atTop (𝓝 0) :=
  covarianceEnergy_tendsto_L1_of_row hμ ν hB hmB hcB v hT
    (hμ.finiteGibbsCovariance_tendsto_fullTimeRowMeanSquare
      hd hb hcrit ν hB hmB hcB v hT).2.2.1

theorem HasFreeIsingLaw.finiteGibbsCovarianceCompensator_tendsto_L1
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (t : ℝ≥0) :
    Tendsto (fun n => eLpNorm
      (finiteGibbsCovarianceCompensator beta v n B t - gibbsCovarianceCompensator beta v B t)
      1 (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) :=
  covarianceCompensator_tendsto_L1_of_energy hμ ν hB hmB hcB v t
    (hμ.finiteGibbsCovarianceEnergy_tendsto_L1 hd hb hcrit ν hB hmB hcB v t.coe_nonneg)

end Problem367

end

end OAI
