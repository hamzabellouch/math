import OAI.Probability.FreeIsing.Conditioning.CovarianceLimit
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

local instance progressiveIsingCovarianceNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

def pairExhaustion {d : ℕ} (v w : TreeVertex d) (n : ℕ) : Finset (TreeVertex d) :=
  connectedExhaustion v (n + w.1.length)

lemma mem_pairExhaustion_left {d : ℕ} (v w : TreeVertex d) (n : ℕ) :
    v ∈ pairExhaustion v w n := mem_connectedExhaustion v _

lemma mem_pairExhaustion_right {d : ℕ} (v w : TreeVertex d) (n : ℕ) :
    w ∈ pairExhaustion v w n := by
  classical
  apply ConnectedHull.subset_hull
  apply Finset.mem_insert_of_mem
  exact (mem_treeBallFinset d (n + w.1.length) w).mpr (by omega)

lemma pairExhaustion_monotone {d : ℕ} (v w : TreeVertex d) :
    Monotone (pairExhaustion v w) := by
  intro n m hnm
  exact connectedExhaustion_monotone v (Nat.add_le_add_right hnm _)

lemma pairExhaustion_connected {d : ℕ} (v w : TreeVertex d) (n : ℕ) :
    ConnectedFinset (pairExhaustion v w n) := connectedExhaustion_connected v _

lemma exists_mem_pairExhaustion {d : ℕ} (v w u : TreeVertex d) :
    ∃ n, u ∈ pairExhaustion v w n := by
  obtain ⟨n, hn⟩ := (eventually_mem_connectedExhaustion v u).exists
  exact ⟨n, connectedExhaustion_monotone v (Nat.le_add_right n _) hn⟩

def finiteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ)
    (y : TreeVertex d → ℝ) : ℝ :=
  FinitePosterior.fieldMean (finiteIsingEnergy beta (pairExhaustion v w n))
    (fun (eta : pairExhaustion v w n → IsingSpin) u => spinSign (eta u))
    (fun eta => spinSign (eta ⟨v, mem_pairExhaustion_left v w n⟩) *
      spinSign (eta ⟨w, mem_pairExhaustion_right v w n⟩))
    ((pairExhaustion v w n).restrict y)

lemma continuous_finiteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ) :
    Continuous (finiteGibbsPairMean beta v w n) := by
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  exact continuous_pi (fun u => continuous_apply u.1)

def infiniteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  max (-1) (min 1 (limUnder atTop (fun n => finiteGibbsPairMean beta v w n y)))

lemma measurable_infiniteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsPairMean beta v w) := by
  have hm : StronglyMeasurable (fun y =>
      limUnder atTop (fun n => finiteGibbsPairMean beta v w n y)) :=
    StronglyMeasurable.limUnder
      (fun n => (continuous_finiteGibbsPairMean beta v w n).measurable.stronglyMeasurable)
  exact measurable_const.max (measurable_const.min hm.measurable)

lemma infiniteGibbsPairMean_abs_le_one {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : |infiniteGibbsPairMean beta v w y| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma spinSign_pair_norm_le_one {d : ℕ} (v w : TreeVertex d)
    (sigma : TreeVertex d → IsingSpin) : ‖spinSign (sigma v) * spinSign (sigma w)‖ ≤ 1 := by
  cases hv : sigma v <;> cases hw : sigma w <;> norm_num [spinSign, hv, hw]

theorem HasFreeIsingLaw.infiniteGibbsPairMean_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsPairMean beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hce (n : ℕ) := hμ.finiteObservation_condExp (pairExhaustion v w n)
    (pairExhaustion_connected v w n) t
    (fun eta => spinSign (eta ⟨v, mem_pairExhaustion_left v w n⟩) *
      spinSign (eta ⟨w, mem_pairExhaustion_right v w n⟩))
  have hlim := tendsto_ae_condExp (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (ℱ := finiteObservationFiltration (pairExhaustion v w)
      (pairExhaustion_monotone v w) t)
    (fun p => spinSign (p.1 v) * spinSign (p.1 w))
  rw [finiteObservationFiltration_iSup (pairExhaustion v w)
    (pairExhaustion_monotone v w) (exists_mem_pairExhaustion v w) t] at hlim
  have hb := ae_bdd_norm_condExp_of_ae_bdd_norm
    (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (m := observationSigma (TreeVertex d) t)
    (Eventually.of_forall (fun p => spinSign_pair_norm_le_one v w p.1))
  filter_upwards [ae_all_iff.mpr hce, hlim, hb] with p hp hlim hb
  have hseq : Tendsto (fun n => finiteGibbsPairMean beta v w n (observation t p)) atTop
      (𝓝 ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] p)) := by
    convert hlim using 1
    ext n
    exact (hp n).symm
  change max (-1) (min 1 (limUnder atTop _)) = _
  rw [hseq.limUnder_eq, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]

theorem isStronglyProgressive_infiniteGibbsPairMean
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v w : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t omega => infiniteGibbsPairMean beta v w (fun i => X i t omega)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_infiniteGibbsPairMean beta v w).comp
    (Measurable.of_eval (fun vertex => (hX vertex t).measurable))).stronglyMeasurable

theorem HasFreeIsingLaw.infiniteGibbsPairMean_eq_brownian_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      infiniteGibbsPairMean beta v w
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) =ᵐ[
        μ.prod (Measure.infinitePi ν)]
      (μ.prod (Measure.infinitePi ν))[fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
          inferInstance] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hpair : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      spinSign (sigma v) * spinSign (sigma w)) :=
    (hsign.comp (measurable_pi_apply v)).mul (hsign.comp (measurable_pi_apply w))
  have hpairi : Integrable (fun sigma : TreeVertex d → IsingSpin =>
      spinSign (sigma v) * spinSign (sigma w)) μ :=
    Integrable.of_bound hpair.aestronglyMeasurable 1
      (Eventually.of_forall (spinSign_pair_norm_le_one v w))
  have hpairpi : Integrable (fun p :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      spinSign (p.1 v) * spinSign (p.1 w))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    Integrable.of_bound (hpair.comp measurable_fst).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => spinSign_pair_norm_le_one v w p.1))
  have hpull := condExp_comp_measurePreserving_comap hT
    (hpair.comp measurable_fst).stronglyMeasurable hpairpi
    (observationSigma_le (TreeVertex d) t)
  have hpast := TerminalSufficiency.condExp_planted_infinite_past_eq_terminal
    μ ν hB hmB (fun sigma i => spinSign (sigma i))
    (fun sigma => spinSign (sigma v) * spinSign (sigma w))
    measurable_spinSign_array hpair hpairi t
  have heq := hμ.infiniteGibbsPairMean_eq_posterior t v w
  rw [← hT.map_eq] at heq
  have heq' := ae_of_ae_map hT.measurable.aemeasurable heq
  rw [hT.map_eq] at heq'
  have hsame : (observationSigma (TreeVertex d) (t : ℝ)).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) inferInstance := by
    rw [observationSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hsame] at hpull
  filter_upwards [hpast, hpull, heq'] with p hpast hpull heq
  simp only [Function.comp_def, T, Prod.map_fst, id_eq] at hpull
  rw [hpast, hpull]
  exact heq

def infiniteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  infiniteGibbsPairMean beta v w y -
    infiniteGibbsSpinMean beta v y * infiniteGibbsSpinMean beta w y

lemma measurable_infiniteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsCovariance beta v w) :=
  (measurable_infiniteGibbsPairMean beta v w).sub
    ((measurable_infiniteGibbsSpinMean beta v).mul
      (measurable_infiniteGibbsSpinMean beta w))

lemma infiniteGibbsCovariance_abs_le_two {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : |infiniteGibbsCovariance beta v w y| ≤ 2 := by
  have hp := infiniteGibbsPairMean_abs_le_one beta v w y
  have hv := infiniteGibbsSpinMean_abs_le_one beta v y
  have hw := infiniteGibbsSpinMean_abs_le_one beta w y
  have hprod : |infiniteGibbsSpinMean beta v y * infiniteGibbsSpinMean beta w y| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul hv hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  exact (abs_sub _ _).trans (by linarith)

theorem HasFreeIsingLaw.infiniteGibbsCovariance_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsCovariance beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (observationSigma (TreeVertex d) t)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) := by
  filter_upwards [hμ.infiniteGibbsPairMean_eq_posterior t v w,
    hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.infiniteGibbsSpinMean_eq_posterior t w] with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp (congrArg₂ (· * ·) hv hw)

def infiniteGibbsResponse {d : ℕ} (beta : ℝ) (v w : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  infiniteGibbsCovariance beta v w y / (1 - infiniteGibbsSpinMean beta v y ^ 2)

lemma measurable_infiniteGibbsResponse {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsResponse beta v w) :=
  (measurable_infiniteGibbsCovariance beta v w).div
    (measurable_const.sub ((measurable_infiniteGibbsSpinMean beta v).pow_const 2))

def infiniteGibbsResponseRow {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  ∑' w, infiniteGibbsResponse beta v w y ^ 2

lemma measurable_infiniteGibbsResponseRow {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    Measurable (infiniteGibbsResponseRow beta v) := by
  exact (StronglyMeasurable.tsum (fun w =>
    ((measurable_infiniteGibbsResponse beta v w).pow_const 2).stronglyMeasurable)).measurable

theorem isStronglyProgressive_infiniteGibbsCovariance
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v w : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t omega => infiniteGibbsCovariance beta v w (fun i => X i t omega)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_infiniteGibbsCovariance beta v w).comp
    (Measurable.of_eval (fun vertex => (hX vertex t).measurable))).stronglyMeasurable

theorem isStronglyProgressive_infiniteGibbsResponseRow
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t omega => infiniteGibbsResponseRow beta v (fun i => X i t omega)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_infiniteGibbsResponseRow beta v).comp
    (Measurable.of_eval (fun vertex => (hX vertex t).measurable))).stronglyMeasurable

theorem HasFreeIsingLaw.infiniteGibbsCovariance_eq_brownian_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      infiniteGibbsCovariance beta v w
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) =ᵐ[
        μ.prod (Measure.infinitePi ν)]
      posteriorCovariance (μ.prod (Measure.infinitePi ν))
        (MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
          inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) := by
  filter_upwards [hμ.infiniteGibbsPairMean_eq_brownian_past ν hB hmB t v w,
    hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t v,
    hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t w] with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp (congrArg₂ (· * ·) hv hw)

theorem HasFreeIsingLaw.exists_bounded_progressive_brownian_covariance
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (v w : TreeVertex d) :
    let F := arrayObservationFiltration B hmB
      (fun sigma i => spinSign (sigma i)) measurable_spinSign_array
    ∃ C : ℝ≥0 → ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ,
      IsStronglyProgressive F C ∧ (∀ t p, |C t p| ≤ 2) ∧
      ∀ t, C t =ᵐ[μ.prod (Measure.infinitePi ν)]
        posteriorCovariance (μ.prod (Measure.infinitePi ν)) (F t)
          (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) := by
  dsimp only
  let X := plantedArrayObservation B
    (fun (sigma : TreeVertex d → IsingSpin) i => spinSign (sigma i))
  let hmX := plantedArrayObservation_measurable hmB
    (measurable_spinSign_array (ι := TreeVertex d))
  refine ⟨fun t p => infiniteGibbsCovariance beta v w (fun i => X i t p), ?_,
    fun t p => infiniteGibbsCovariance_abs_le_two beta v w _, ?_⟩
  · apply isStronglyProgressive_infiniteGibbsCovariance
    intro i
    apply (arrayNaturalFiltration_stronglyAdapted X hmX i).isStronglyProgressive_of_continuous
    intro p
    exact (hcB i (p.2 i)).add (continuous_subtype_val.mul continuous_const)
  · intro t
    have heq := hμ.infiniteGibbsCovariance_eq_brownian_past ν hB hmB t v w
    simpa only [arrayObservationFiltration, arrayNaturalFiltration_eq_comap,
      X, plantedArrayObservation, add_comm] using heq

lemma finiteGibbsPairMean_self {d : ℕ} (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (y : TreeVertex d → ℝ) : finiteGibbsPairMean beta v v n y = 1 := by
  unfold finiteGibbsPairMean
  have heq : (fun eta : pairExhaustion v v n → IsingSpin =>
      spinSign (eta ⟨v, mem_pairExhaustion_left v v n⟩) *
        spinSign (eta ⟨v, mem_pairExhaustion_right v v n⟩)) = fun _ => (1 : ℝ) := by
    funext eta
    cases h : eta ⟨v, mem_pairExhaustion_left v v n⟩ <;> simp [spinSign]
  rw [heq, FinitePosterior.fieldMean_const]

lemma infiniteGibbsPairMean_self {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : infiniteGibbsPairMean beta v v y = 1 := by
  unfold infiniteGibbsPairMean
  simp only [finiteGibbsPairMean_self]
  rw [tendsto_const_nhds.limUnder_eq]
  norm_num

lemma infiniteGibbsCovariance_self {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) :
    infiniteGibbsCovariance beta v v y = 1 - infiniteGibbsSpinMean beta v y ^ 2 := by
  rw [infiniteGibbsCovariance, infiniteGibbsPairMean_self, pow_two]

theorem HasFreeIsingLaw.infiniteGibbsResponse_self_brownian
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      0 < 1 - infiniteGibbsSpinMean beta v y ^ 2 ∧
        infiniteGibbsResponse beta v v y = 1 := by
  filter_upwards [hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta ν hB hmB t v]
    with p hp
  dsimp only at hp ⊢
  have hpos : 0 < 1 - infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2 := by
    nlinarith [hp.1.1, hp.1.2]
  refine ⟨hpos, ?_⟩
  rw [infiniteGibbsResponse, infiniteGibbsCovariance_self, div_self hpos.ne']

end Problem367

end

end OAI
