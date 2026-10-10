import OAI.Probability.FreeIsing.Brownian.RowComparisonConstruction
import OAI.Probability.FreeIsing.Gibbs.CovarianceStrictConvergence
import OAI.Probability.FreeIsing.Gibbs.CovarianceUniformEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.PredictableL2

theorem row_meanSquare_cauchy_of_tendsto
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → ι → Ω → ℝ} {Y : ι → Ω → ℝ}
    (hX : ∀ n a, MemLp (X n a) 2 P) (hY : ∀ a, MemLp (Y a) 2 P)
    (hs : ∀ n, Summable fun a => ∫ ω, (X n a ω - Y a ω) ^ 2 ∂P)
    (hl : Tendsto (fun n => ∑' a, ∫ ω, (X n a ω - Y a ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    (∀ n k, Summable fun a => ∫ ω, (X n a ω - X k a ω) ^ 2 ∂P) ∧
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
        (∑' a, ∫ ω, (X n a ω - X k a ω) ^ 2 ∂P) < ε := by
  have hb (n k : ℕ) (a : ι) :=
    BrownianGrid.integral_sq_sub_le_two (hX n a) (hX k a) (hY a)
  have hs' (n k : ℕ) : Summable fun a =>
      ∫ ω, (X n a ω - X k a ω) ^ 2 ∂P := by
    apply Summable.of_nonneg_of_le
      (fun a => integral_nonneg fun ω => sq_nonneg _) _
      (((hs n).mul_left 2).add ((hs k).mul_left 2))
    intro a
    exact hb n k a
  have hbound (n k : ℕ) :
      (∑' a, ∫ ω, (X n a ω - X k a ω) ^ 2 ∂P) ≤
      2 * (∑' a, ∫ ω, (X n a ω - Y a ω) ^ 2 ∂P) +
      2 * (∑' a, ∫ ω, (X k a ω - Y a ω) ^ 2 ∂P) := by
    have h := Summable.tsum_le_tsum (fun a => by
      exact hb n k a)
      (hs' n k) (((hs n).mul_left 2).add ((hs k).mul_left 2))
    simpa only [Summable.tsum_add ((hs n).mul_left 2) ((hs k).mul_left 2),
      tsum_mul_left] using h
  refine ⟨hs', fun ε hε => ?_⟩
  have hsmall : ∀ᶠ n in atTop,
      (∑' a, ∫ ω, (X n a ω - Y a ω) ^ 2 ∂P) < ε / 4 :=
    hl.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨N, fun n hn k hk => ?_⟩
  have hn' := hN n hn
  have hk' := hN k hk
  linarith [hbound n k]

end Problem367.PredictableL2

namespace Problem367

theorem HasFreeIsingLaw.finiteGibbsCovariance_energy_cauchy_of_strict
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
    let X := fun p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)
    let C := fun n w p => finiteGibbsCovariance beta v w n (X p)
    (∀ n k, Summable fun w => ∫ p, (C n w p - C k w p) ^ 2 ∂P) ∧
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
        (∑' w, ∫ p, (C n w p - C k w p) ^ 2 ∂P) < ε := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := τ.prod (μ.prod (Measure.infinitePi ν))
  let X := fun p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
    fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)
  have hX : Measurable X := measurable_brownian_ising_observation_uncurry hmB hcB
  have hf (n : ℕ) (w : TreeVertex d) :
      MemLp (fun p => finiteGibbsCovariance beta v w n (X p)) 2 P :=
    (memLp_two_iff_integrable_sq
      (((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).aestronglyMeasurable)).2
      (integrable_finiteGibbsCovariance_sq beta v w n hX)
  have hi (w : TreeVertex d) : MemLp (fun p => infiniteGibbsCovariance beta v w (X p)) 2 P :=
    (memLp_two_iff_integrable_sq
      (((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)).2
      (integrable_infiniteGibbsCovariance_sq beta v w hX)
  have hr := hμ.finiteGibbsCovariance_brownian_tendsto_timeRowMeanSquare_of_strict
    hb hstrict ν hB hmB hcB τ v
  exact PredictableL2.row_meanSquare_cauchy_of_tendsto hf hi hr.1 hr.2.2.1

open PlantedSymmetry GaussianTreeCovariance

theorem HasFreeIsingLaw.finiteGibbsCovariance_energy_cauchy_away_zero
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ] {δ : ℝ≥0} (hδ : 0 < δ)
    (hτ : ∀ᵐ t ∂τ, δ ≤ t) (v : TreeVertex d) :
    let P := τ.prod (μ.prod (Measure.infinitePi ν))
    let X := fun p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)
    let C := fun n w p => finiteGibbsCovariance beta v w n (X p)
    (∀ n k, Summable fun w => ∫ p, (C n w p - C k w p) ^ 2 ∂P) ∧
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
        (∑' w, ∫ p, (C n w p - C k w p) ^ 2 ∂P) < ε := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := τ.prod (μ.prod (Measure.infinitePi ν))
  let X := fun p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
    fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)
  have hX : Measurable X := measurable_brownian_ising_observation_uncurry hmB hcB
  have hf (n : ℕ) (w : TreeVertex d) :
      MemLp (fun p => finiteGibbsCovariance beta v w n (X p)) 2 P :=
    (memLp_two_iff_integrable_sq
      (((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).aestronglyMeasurable)).2
      (integrable_finiteGibbsCovariance_sq beta v w n hX)
  have hi (w : TreeVertex d) : MemLp (fun p => infiniteGibbsCovariance beta v w (X p)) 2 P :=
    (memLp_two_iff_integrable_sq
      (((measurable_infiniteGibbsCovariance beta v w).comp hX).aestronglyMeasurable)).2
      (integrable_infiniteGibbsCovariance_sq beta v w hX)
  have hs (n : ℕ) : Summable fun w =>
      ∫ p, (finiteGibbsCovariance beta v w n (X p) - infiniteGibbsCovariance beta v w (X p)) ^ 2 ∂P :=
    Summable.of_nonneg_of_le (fun w => integral_nonneg fun p => sq_nonneg _)
      (fun w => hμ.integral_covarianceError_time_le hb ν hB hmB hcB τ hδ hτ v w n)
      ((summable_geometric_intrinsic v
        (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)
        (gaussian_radial_ratio_lt_one hδ hcrit)).mul_left (4 * τ.real Set.univ))
  exact PredictableL2.row_meanSquare_cauchy_of_tendsto hf hi hs
    (hμ.finiteGibbsCovariance_brownian_tendsto_timeRowMeanSquare
      hb ν hB hmB hcB τ hδ hτ hcrit v)

end Problem367

end

end OAI
