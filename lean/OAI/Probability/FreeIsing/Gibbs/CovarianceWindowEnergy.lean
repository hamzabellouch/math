import OAI.Probability.FreeIsing.Gibbs.CovarianceStrictEnergy
import OAI.Probability.FreeIsing.Gibbs.CovarianceUniformEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry GaussianTreeCovariance

lemma integral_prod_Ioc_sub {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [SFinite ρ] {f : ℝ × Ω → ℝ} {δ T : ℝ}
    (hδ : 0 ≤ δ) (hδT : δ ≤ T)
    (hf : Integrable f ((volume.restrict (Ioc (0 : ℝ) T)).prod ρ)) :
    (∫ p, f p ∂(volume.restrict (Ioc δ T)).prod ρ) =
      (∫ p, f p ∂(volume.restrict (Ioc (0 : ℝ) T)).prod ρ) -
      ∫ p, f p ∂(volume.restrict (Ioc (0 : ℝ) δ)).prod ρ := by
  have hm : (volume.restrict (Ioc (0 : ℝ) T)).prod ρ =
      (volume.restrict (Ioc (0 : ℝ) δ)).prod ρ +
        (volume.restrict (Ioc δ T)).prod ρ := by
    rw [← Ioc_union_Ioc_eq_Ioc hδ hδT,
      Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.add_prod]
  rw [hm, integrable_add_measure] at hf
  rw [hm, integral_add_measure hf.1 hf.2]
  ring

lemma finiteGibbsCovariance_tsum_integral_eq {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ) [IsFiniteMeasure τ] :
    (∑' w, ∫ p, finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) =
    ∫ p, ∑ w ∈ connectedExhaustion v n,
      finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν)) := by
  classical
  rw [tsum_eq_sum (s := connectedExhaustion v n)]
  · exact (integral_finsetSum _ (fun w _ =>
      integrable_finiteGibbsCovariance_sq beta v w n
        (measurable_brownianIsingObservationR hmB hcB))).symm
  · intro w hw
    simp only [finiteGibbsCovariance, dite_eq_right hw, zero_pow (by decide : 2 ≠ 0), integral_zero]

theorem HasFreeIsingLaw.finiteGibbsCovariance_windowEnergy_eq
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) (n : ℕ) {δ T : ℝ} (hδ : 0 ≤ δ) (hδT : δ ≤ T) :
    (∑' w, ∫ p, finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
      ∂(volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν))) =
    (∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (T, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) -
    ∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (δ, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  rw [finiteGibbsCovariance_tsum_integral_eq beta v n μ ν hmB hcB]
  rw [integral_prod_Ioc_sub hδ hδT (integrable_finsetSum _ (fun w _ =>
    integrable_finiteGibbsCovariance_sq beta v w n
      (measurable_brownianIsingObservationR hmB hcB)))]
  rw [← finiteGibbsCovariance_tsum_integral_eq beta v n μ ν hmB hcB,
    ← finiteGibbsCovariance_tsum_integral_eq beta v n μ ν hmB hcB,
    hμ.finiteGibbsCovariance_timeEnergy_eq ν hB hmB hcB v n (hδ.trans hδT),
    hμ.finiteGibbsCovariance_timeEnergy_eq ν hB hmB hcB v n hδ]

theorem HasFreeIsingLaw.finiteGibbsCovariance_tendsto_windowSquareIntegral
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v w : TreeVertex d) {δ T : ℝ} (hδ : 0 ≤ δ) (hδT : δ ≤ T) :
    Tendsto (fun n => ∫ p,
      finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
      ∂(volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν))) atTop
    (𝓝 (∫ p, infiniteGibbsCovariance beta v w (brownianIsingObservationR B p) ^ 2
      ∂(volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hX := measurable_brownianIsingObservationR hmB hcB
  simp_rw [integral_prod_Ioc_sub hδ hδT
    (integrable_finiteGibbsCovariance_sq beta v w _ hX),
    integral_prod_Ioc_sub hδ hδT (integrable_infiniteGibbsCovariance_sq beta v w hX)]
  exact (hμ.finiteGibbsCovariance_tendsto_timeSquareIntegral ν hB hmB hcB v w).sub
    (hμ.finiteGibbsCovariance_tendsto_timeSquareIntegral ν hB hmB hcB v w)

theorem integral_finiteGibbsCovariance_window_sq_le_distance
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (hb : 0 ≤ beta) (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    {δ T : ℝ} (hδ : 0 < δ) (v w : TreeVertex d) (n : ℕ) :
    (∫ p, finiteGibbsCovariance beta v w n (brownianIsingObservationR B p) ^ 2
      ∂(volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν))) ≤
      (volume.restrict (Ioc δ T)).real univ *
        (Real.tanh beta ^ 2 * gaussianContraction beta δ.toNNReal) ^
          reducedWordDistance v.1 w.1 := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hi := integrable_finiteGibbsCovariance_sq beta v w n
    (P := (volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν)))
    (measurable_brownianIsingObservationR hmB hcB)
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _t,
        (Real.tanh beta ^ 2 * gaussianContraction beta δ.toNNReal) ^
          reducedWordDistance v.1 w.1 ∂volume.restrict (Ioc δ T) := by
      apply integral_mono_ae hi.integral_prod_left (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 ≤ t := hδ.le.trans ht.1.le
      have heq := integral_brownian_ising_observation_eq_gaussian μ ν hB hmB t.toNNReal
        (fun y => finiteGibbsCovariance beta v w n y ^ 2)
        ((continuous_finiteGibbsCovariance beta v w n).measurable.pow_const 2)
      rw [Real.coe_toNNReal t ht0] at heq
      change (∫ p, finiteGibbsCovariance beta v w n
        (fun i => t * spinSign (p.1 i) + B i t.toNNReal (p.2 i)) ^ 2
        ∂μ.prod (Measure.infinitePi ν)) ≤ _
      rw [heq]
      simpa only [Real.coe_toNNReal t ht0] using
        integral_finiteGibbsCovariance_sq_le_distance μ hb
          (Real.toNNReal_pos.mpr hδ) (Real.toNNReal_mono ht.1.le) v w n
    _ = _ := by rw [integral_const, smul_eq_mul]

theorem HasFreeIsingLaw.infiniteGibbsCovariance_windowEnergy_eq
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {δ T : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) :
    let P := (volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν))
    let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
    let M := fun t => ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (t, p)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)
    HasSum (fun w => ∫ p, C w p ^ 2 ∂P) (M T - M δ) ∧
      (∫ p, ∑' w, C w p ^ 2 ∂P) = M T - M δ := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν))
  let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
  let Cn := fun n w p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)
  let M := fun t => ∫ p, infiniteGibbsSpinMean beta v (brownianIsingObservationR B (t, p)) ^ 2
    ∂μ.prod (Measure.infinitePi ν)
  let Mn := fun n t => ∫ p, finiteGibbsSpinMean beta v n (brownianIsingObservationR B (t, p)) ^ 2
    ∂μ.prod (Measure.infinitePi ν)
  let b := fun w : TreeVertex d => (volume.restrict (Ioc δ T)).real univ *
    (Real.tanh beta ^ 2 * gaussianContraction beta δ.toNNReal) ^ reducedWordDistance v.1 w.1
  have hs : Summable b :=
    (summable_geometric_intrinsic v
      (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ.toNNReal).le)
      (gaussian_radial_ratio_lt_one (Real.toNNReal_pos.mpr hδ) hcrit)).mul_left _
  have hbound (n : ℕ) (w : TreeVertex d) : (∫ p, Cn n w p ^ 2 ∂P) ≤ b w :=
    integral_finiteGibbsCovariance_window_sq_le_distance μ hb ν hB hmB hcB hδ v w n
  have hcoord (w : TreeVertex d) :
      Tendsto (fun n => ∫ p, Cn n w p ^ 2 ∂P) atTop (𝓝 (∫ p, C w p ^ 2 ∂P)) :=
    hμ.finiteGibbsCovariance_tendsto_windowSquareIntegral ν hB hmB hcB v w hδ.le hδT
  have hlim : Tendsto (fun n => ∑' w, ∫ p, Cn n w p ^ 2 ∂P) atTop
      (𝓝 (∑' w, ∫ p, C w p ^ 2 ∂P)) := by
    apply tendsto_tsum_of_dominated_convergence hs hcoord
    exact Eventually.of_forall fun n w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => sq_nonneg _))]
      exact hbound n w
  have hterminal (t : ℝ) (ht : 0 ≤ t) : Tendsto (fun n => Mn n t) atTop (𝓝 (M t)) := by
    have h := hμ.finiteGibbsSpinMean_brownian_tendsto_integral_sq ν hB hmB t.toNNReal v
    rw [Real.coe_toNNReal t ht] at h
    convert h using 1 <;> rfl
  have hfinite (n : ℕ) : (∑' w, ∫ p, Cn n w p ^ 2 ∂P) = Mn n T - Mn n δ :=
    hμ.finiteGibbsCovariance_windowEnergy_eq ν hB hmB hcB v n hδ.le hδT
  have heq : (∑' w, ∫ p, C w p ^ 2 ∂P) = M T - M δ :=
    tendsto_nhds_unique hlim
      (((hterminal T (hδ.le.trans hδT)).sub (hterminal δ hδ.le)).congr'
        (Eventually.of_forall fun n => (hfinite n).symm))
  have hsum : Summable (fun w => ∫ p, C w p ^ 2 ∂P) :=
    Summable.of_nonneg_of_le (fun w => integral_nonneg (fun p => sq_nonneg _))
      (fun w => le_of_tendsto (hcoord w) (Eventually.of_forall fun n => hbound n w)) hs
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hrow := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun w => integrable_infiniteGibbsCovariance_sq beta v w hX (P := P)) hsum
  have hident := DiscrepancyEnergy.hasSum_integral_sq_row
    (fun w => ((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)
    hrow.1 hrow.2
  have hh : HasSum (fun w => ∫ p, C w p ^ 2 ∂P) (M T - M δ) := by
    rw [← heq]
    exact hsum.hasSum
  dsimp only
  exact ⟨hh, hident.unique hh⟩

end Problem367

end

end OAI
