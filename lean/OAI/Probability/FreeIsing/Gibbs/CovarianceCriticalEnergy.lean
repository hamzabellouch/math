import OAI.Probability.FreeIsing.Gaussian.SiteInformation
import OAI.Probability.FreeIsing.Gibbs.CovarianceWindowEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_secondMoment
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : TreeVertex d) :
    (∫ p, infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤
      ((1 + Real.tanh beta ^ 2) *
        Real.sqrt (1 / ((1 - Real.tanh beta ^ 2) * Real.tanh beta ^ 4))) *
          Real.sqrt (t : ℝ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  rw [integral_brownian_ising_observation_eq_gaussian μ ν hB hmB t
    (fun y => infiniteGibbsSpinMean beta v y ^ 2)
    ((measurable_infiniteGibbsSpinMean beta v).pow_const 2)]
  exact hμ.infiniteGibbsSpinMean_critical_secondMoment hd hb hcritical t ht v

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (v : TreeVertex d) :
    Tendsto (fun t : ℝ≥0 => ∫ p, infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) (𝓝 0) (𝓝 0) := by
  let K := (1 + Real.tanh beta ^ 2) *
    Real.sqrt (1 / ((1 - Real.tanh beta ^ 2) * Real.tanh beta ^ 4))
  have hlim : Tendsto (fun t : ℝ≥0 => K * Real.sqrt (t : ℝ)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ≥0 => K * Real.sqrt (t : ℝ)) := by fun_prop
    simpa only [NNReal.coe_zero, Real.sqrt_zero, mul_zero] using
      hc.tendsto (0 : ℝ≥0)
  apply squeeze_zero' (Eventually.of_forall fun t => integral_nonneg (fun p => sq_nonneg _)) _ hlim
  have ht : ∀ᶠ t : ℝ≥0 in 𝓝 0, (t : ℝ) < 1 :=
    (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).eventually (eventually_lt_nhds (by norm_num))
  exact ht.mono fun t ht =>
    hμ.infiniteGibbsSpinMean_brownian_critical_secondMoment hd hb hcritical ν hB hmB t ht.le v

lemma HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (v : TreeVertex d) :
    (∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (0, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) = 0 := by
  have h := hμ.infiniteGibbsSpinMean_brownian_critical_secondMoment
    hd hb hcritical ν hB hmB 0 (by norm_num) v
  simp only [NNReal.coe_zero, Real.sqrt_zero, mul_zero] at h
  unfold brownianIsingObservationR
  dsimp only
  rw [Real.toNNReal_zero]
  exact le_antisymm h (integral_nonneg (fun p => sq_nonneg _))

theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq_of_critical
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)
    HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) = M := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let P := fun t : ℝ => (volume.restrict (Ioc (0 : ℝ) t)).prod ρ
  let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
  let E := fun t : ℝ => ∫ p, ∑' w, C w p ^ 2 ∂P t
  let M := fun t : ℝ => ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (t, p)) ^ 2 ∂ρ
  have hrow (t : ℝ) (ht : 0 ≤ t) := hμ.infiniteGibbsCovariance_timeEnergy ν hB hmB hcB v ht
  have hi (t : ℝ) (ht : 0 ≤ t) : Integrable (fun p => ∑' w, C w p ^ 2) (P t) :=
    (hrow t ht).2.2.2.1
  have heq : E T = M T := by
    rcases eq_or_lt_of_le hT with hzero | hpos
    · subst T
      have hM0 : M 0 = 0 := hμ.infiniteGibbsSpinMean_brownian_critical_zero
        hd hb hcritical ν hB hmB v
      simp only [E, P, Ioc_self, Measure.restrict_empty, Measure.zero_prod, integral_zero_measure, hM0]
    · let δ := fun n : ℕ => T / ((n : ℝ) + 1)
      have hδpos (n : ℕ) : 0 < δ n := div_pos hpos (by positivity)
      have hδT (n : ℕ) : δ n ≤ T := by
        dsimp [δ]
        exact div_le_self hT (le_add_of_nonneg_left (Nat.cast_nonneg n))
      have hδlim : Tendsto δ atTop (𝓝 0) := by
        simpa only [δ, mul_one_div, mul_zero] using
          (tendsto_const_nhds (x := T)).mul
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hMlim : Tendsto (fun n => M (δ n)) atTop (𝓝 0) := by
        have hn : Tendsto (fun n => (δ n).toNNReal) atTop (𝓝 0) := by
          simpa only [Function.comp_def, Real.toNNReal_zero] using
            (continuous_real_toNNReal.tendsto 0).comp hδlim
        have h := (hμ.infiniteGibbsSpinMean_brownian_critical_tendsto_zero
          hd hb hcritical ν hB hmB v).comp hn
        convert h using 1
        funext n
        simp only [Function.comp_def, M, ρ,
          Real.coe_toNNReal (δ n) (hδpos n).le]
        rfl
      let f := fun t : ℝ => ∫ p, ∑' w, C w (t, p) ^ 2 ∂ρ
      have hf : Integrable f (volume.restrict (Ioc (0 : ℝ) T)) :=
        (hi T hT).integral_prod_left
      have hprim := (hf.continuous_primitive 0).tendsto 0
      have hElim : Tendsto (fun n => E (δ n)) atTop (𝓝 0) := by
        have h := hprim.comp hδlim
        simp only [intervalIntegral.integral_same] at h
        convert h using 1
        funext n
        dsimp only [E, Function.comp_def]
        rw [integral_prod _ (hi (δ n) (hδpos n).le),
          intervalIntegral.integral_of_le (hδpos n).le,
          Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.mpr (Ioc_subset_Ioc_right (hδT n))]
      have hdiff (n : ℕ) : E T - E (δ n) = M T - M (δ n) := by
        have hw := (hμ.infiniteGibbsCovariance_windowEnergy_eq hb hcritical.le
          ν hB hmB hcB v (hδpos n) (hδT n)).2
        exact (integral_prod_Ioc_sub (hδpos n).le (hδT n) (hi T hT)).symm.trans hw
      have hsame := tendsto_nhds_unique
        ((tendsto_const_nhds (x := E T)).sub hElim)
        (((tendsto_const_nhds (x := M T)).sub hMlim).congr'
          (Eventually.of_forall fun n => (hdiff n).symm))
      simpa only [sub_zero] using hsame
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hident := DiscrepancyEnergy.hasSum_integral_sq_row
    (fun w => ((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)
    (hrow T hT).2.2.1 (hi T hT)
  have hh : HasSum (fun w => ∫ p, C w p ^ 2 ∂P T) (M T) := by
    rw [← heq]
    exact hident
  dsimp only
  exact ⟨hh, heq⟩

theorem HasFreeIsingLaw.infiniteGibbsCovariance_timeEnergy_eq
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    let M := ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)
    HasSum (fun w => ∫ p, C w p ^ 2 ∂P) M ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) = M := by
  rcases lt_or_eq_of_le hcrit with hs | he
  · exact hμ.infiniteGibbsCovariance_timeEnergy_eq_of_strict hb hs ν hB hmB hcB v hT
  · exact hμ.infiniteGibbsCovariance_timeEnergy_eq_of_critical hd hb he ν hB hmB hcB v hT

end Problem367

end

end OAI
