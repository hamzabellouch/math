import OAI.Probability.FreeIsing.Gibbs.CovarianceIntrinsicEnergy
import OAI.Probability.FreeIsing.Trees.GibbsCovariance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace Problem367
open PlantedSymmetry

theorem finiteGibbsCovariance_abs_le_distance {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) (v w : TreeVertex d) (n : ℕ) (y : TreeVertex d → ℝ) :
    |finiteGibbsCovariance beta v w n y| ≤
      Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
  classical
  unfold finiteGibbsCovariance
  split_ifs with hw
  · rw [finiteGibbsCovarianceOn_eq_treeCovariance]
    simp only [TreePathResponse.covariance,
      extendFiniteSpin_apply (connectedExhaustion v n) _ ⟨v, mem_connectedExhaustion v n⟩,
      extendFiniteSpin_apply (connectedExhaustion v n) _ ⟨w, hw⟩]
    exact abs_tree_gibbs_covariance_le hb (connectedExhaustion_connected v n) y
        (mem_connectedExhaustion v n) hw
  · simpa only [abs_zero] using
      pow_nonneg (tanh_nonneg_of_beta_nonneg hb) (reducedWordDistance v.1 w.1)

theorem HasFreeIsingLaw.infiniteGibbsCovariance_brownian_abs_le_distance
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      |infiniteGibbsCovariance beta v w
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))| ≤
          Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
  filter_upwards [hμ.finiteGibbsCovariance_brownian_tendsto_ae ν hB hmB t v w]
    with p hp
  exact le_of_tendsto hp.abs (Eventually.of_forall fun n =>
    finiteGibbsCovariance_abs_le_distance hb v w n _)

theorem HasFreeIsingLaw.finiteGibbsCovariance_brownian_time_error_le
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ] (v w : TreeVertex d) (n : ℕ) :
    (∫ p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
      (finiteGibbsCovariance beta v w n
          (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)) -
        infiniteGibbsCovariance beta v w
          (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i))) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) ≤
      (τ.prod (μ.prod (Measure.infinitePi ν))).real Set.univ * 4 *
        (Real.tanh beta ^ 2) ^ reducedWordDistance v.1 w.1 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let X := fun p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
    fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)
  have hX : Measurable X := measurable_brownian_ising_observation_uncurry hmB hcB
  have hinf : ∀ᵐ p ∂τ.prod (μ.prod (Measure.infinitePi ν)),
      |infiniteGibbsCovariance beta v w (X p)| ≤
        Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
      (((measurable_infiniteGibbsCovariance beta v w).comp hX).abs) measurable_const)).2
    exact Eventually.of_forall fun t =>
      hμ.infiniteGibbsCovariance_brownian_abs_le_distance hb ν hB hmB t v w
  calc
    _ ≤ ∫ _p, (2 * Real.tanh beta ^ reducedWordDistance v.1 w.1) ^ 2
        ∂τ.prod (μ.prod (Measure.infinitePi ν)) := by
      apply integral_mono_ae
        (integrable_finiteGibbsCovariance_sub_infinite_sq beta v w n hX) (integrable_const _)
      filter_upwards [hinf] with p hp
      have hf := finiteGibbsCovariance_abs_le_distance hb v w n (X p)
      have hsub := (abs_sub (finiteGibbsCovariance beta v w n (X p))
        (infiniteGibbsCovariance beta v w (X p))).trans (add_le_add hf hp)
      have hs := pow_le_pow_left₀ (abs_nonneg _) hsub 2
      simpa only [sq_abs, ← two_mul] using hs
    _ = _ := by
      rw [integral_const, smul_eq_mul, mul_pow, ← pow_mul]
      rw [Nat.mul_comm (reducedWordDistance v.1 w.1) 2, pow_mul]
      ring

theorem HasFreeIsingLaw.finiteGibbsCovariance_brownian_tendsto_timeRowMeanSquare_of_strict
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ] (v : TreeVertex d) :
    let P := τ.prod (μ.prod (Measure.infinitePi ν))
    let err := fun n w p =>
      (finiteGibbsCovariance beta v w n
          (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)) -
        infiniteGibbsCovariance beta v w
          (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i))) ^ 2
    (∀ n, Summable (fun w => ∫ p, err n w p ∂P)) ∧
      (∀ n, Integrable (fun p => ∑' w, err n w p) P) ∧
      Tendsto (fun n => ∑' w, ∫ p, err n w p ∂P) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ p, ∑' w, err n w p ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  dsimp only
  let P := τ.prod (μ.prod (Measure.infinitePi ν))
  let X := fun p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
    fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)
  let err := fun n w p =>
    (finiteGibbsCovariance beta v w n (X p) - infiniteGibbsCovariance beta v w (X p)) ^ 2
  have hX : Measurable X := measurable_brownian_ising_observation_uncurry hmB hcB
  have hi (n : ℕ) (w : TreeVertex d) : Integrable (err n w) P :=
    integrable_finiteGibbsCovariance_sub_infinite_sq beta v w n hX
  have hbnd (n : ℕ) (w : TreeVertex d) :
      (∫ p, err n w p ∂P) ≤ P.real Set.univ * 4 *
        (Real.tanh beta ^ 2) ^ reducedWordDistance v.1 w.1 :=
    hμ.finiteGibbsCovariance_brownian_time_error_le hb ν hB hmB hcB τ v w n
  have hs := (summable_geometric_intrinsic v (sq_nonneg (Real.tanh beta)) hstrict).mul_left
    (P.real Set.univ * 4)
  have hsum (n : ℕ) : Summable (fun w => ∫ p, err n w p ∂P) :=
    Summable.of_nonneg_of_le (fun w => integral_nonneg (fun p => sq_nonneg _)) (hbnd n) hs
  have hnorm (n : ℕ) : Summable (fun w => ∫ p, ‖err n w p‖ ∂P) := by
    simpa only [err, Real.norm_eq_abs, abs_pow, sq_abs] using hsum n
  have hconv : Tendsto (fun n => ∑' w, ∫ p, err n w p ∂P) atTop (𝓝 0) := by
    have hlim := tendsto_tsum_of_dominated_convergence hs
      (fun w => hμ.finiteGibbsCovariance_brownian_tendsto_timeMeanSquare ν hB hmB hcB τ v w)
      (Eventually.of_forall fun n w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => sq_nonneg _))]
        exact hbnd n w)
    simpa only [tsum_zero] using hlim
  refine ⟨hsum, ?_, hconv, ?_⟩
  · intro n
    exact (DiscrepancyEnergy.sq_row_integrable_of_summable_integrals (hi n) (hsum n)).2
  · have heq (n : ℕ) : (∫ p, ∑' w, err n w p ∂P) = ∑' w, ∫ p, err n w p ∂P :=
      (integral_tsum_of_summable_integral_norm (hi n) (hnorm n)).symm
    change Tendsto (fun n => ∫ p, ∑' w, err n w p ∂P) atTop (𝓝 0)
    simp_rw [heq]
    exact hconv

end Problem367

end

end OAI
