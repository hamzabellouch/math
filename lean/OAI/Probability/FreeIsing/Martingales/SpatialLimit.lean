import OAI.Probability.FreeIsing.Estimates.ContinuousHorizonGluing
import OAI.Probability.FreeIsing.Martingales.L2Closure
import OAI.Probability.FreeIsing.Martingales.PredictableL2Completion
import OAI.Probability.FreeIsing.Martingales.StrongMaximal

namespace OAI

noncomputable section

open MeasureTheory Filter Finset
open scoped NNReal Topology

namespace Problem367.MartingaleSpatialLimit

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def finiteSum (M : ι → ℝ≥0 → Ω → ℝ) (s : Finset ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ s, M i t ω

theorem finiteSum_memLp {M : ι → ℝ≥0 → Ω → ℝ}
    (h2 : ∀ i t, MemLp (M i t) 2 μ) (s : Finset ι) (t : ℝ≥0) :
    MemLp (finiteSum M s t) 2 μ :=
  memLp_finsetSum s (fun i _ => h2 i t)

theorem finiteSum_martingale {F : Filtration ℝ≥0 mΩ} {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (s : Finset ι) :
    Martingale (finiteSum M s) F μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have heq : finiteSum M ∅ = 0 := by funext t ω; simp [finiteSum]
    rw [heq]
    exact martingale_zero ℝ F μ
  | @insert i s hi ih =>
    have heq : finiteSum M (insert i s) = M i + finiteSum M s := by
      funext t ω
      simp only [finiteSum, sum_insert hi, Pi.add_apply]
    rw [heq]
    exact (hM i).add ih

theorem finiteSum_ae_continuous {M : ι → ℝ≥0 → Ω → ℝ}
    (hc : ∀ i, ∀ᵐ ω ∂μ, Continuous (fun t => M i t ω)) (s : Finset ι) :
    ∀ᵐ ω ∂μ, Continuous (fun t => finiteSum M s t ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ i ∈ s, Continuous (fun t => M i t ω) :=
    (Filter.eventually_all_finite s.finite_toSet).mpr (fun i _ => hc i)
  filter_upwards [hall] with ω hω
  exact continuous_finsetSum s hω

theorem summable_energy_of_integer [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (h2 : ∀ i t, MemLp (M i t) 2 μ)
    (henergy : ∀ N : ℕ, Summable (fun i => ∫ ω, M i (N : ℝ≥0) ω ^ 2 ∂μ))
    (t : ℝ≥0) : Summable (fun i => ∫ ω, M i t ω ^ 2 ∂μ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge t
  exact Summable.of_nonneg_of_le (fun i => integral_nonneg (fun ω => sq_nonneg _))
    (fun i => MartingaleSquareMaximal.integral_sq_le (hM i) (h2 i) hN) (henergy N)

theorem summable_toLp {M : ι → ℝ≥0 → Ω → ℝ}
    (h2 : ∀ i t, MemLp (M i t) 2 μ) (t : ℝ≥0)
    (horth : Pairwise (fun i j => ∫ ω, M i t ω * M j t ω ∂μ = 0))
    (henergy : Summable (fun i => ∫ ω, M i t ω ^ 2 ∂μ)) :
    Summable (fun i => (h2 i t).toLp (M i t)) := by
  apply PredictableL2.summable_of_orthogonal_sq
  · intro i j hij
    simpa only [PredictableL2.inner_toLp] using horth hij
  · simpa only [PredictableL2.norm_toLp_sq] using henergy

theorem exists_continuous_martingale_sum [Countable ι] [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ι → ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ)
    (h2 : ∀ i t, MemLp (M i t) 2 μ)
    (hc : ∀ i, ∀ᵐ ω ∂μ, Continuous (fun t => M i t ω))
    (horth : ∀ t, Pairwise (fun i j => ∫ ω, M i t ω * M j t ω ∂μ = 0))
    (henergy : ∀ N : ℕ, Summable (fun i => ∫ ω, M i (N : ℝ≥0) ω ^ 2 ∂μ)) :
    ∃ (L : ℝ≥0 → Ω → ℝ) (hL2 : ∀ t, MemLp (L t) 2 μ),
      IsStronglyPredictable F L ∧ Martingale L F μ ∧
      (∀ᵐ ω ∂μ, Continuous (fun t => L t ω)) ∧
      (∀ t, HasSum (fun i => (h2 i t).toLp (M i t)) ((hL2 t).toLp (L t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun s : Finset ι =>
        ∫ ω, MartingaleStrongMaximal.maximalSquare (finiteSum M s - L) T ω ∂μ)
        atTop (𝓝 0)) := by
  classical
  obtain ⟨s, hs⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
  have hsum (t : ℝ≥0) : Summable (fun i => (h2 i t).toLp (M i t)) :=
    summable_toLp h2 t (horth t) (summable_energy_of_integer hM h2 henergy t)
  have heq (n : ℕ) (t : ℝ≥0) :
      (finiteSum_memLp h2 (s n) t).toLp (finiteSum M (s n) t) =
        ∑ i ∈ s n, (h2 i t).toLp (M i t) :=
    PredictableL2.toLp_finsetSum (fun i => M i t) (fun i => h2 i t) (s n)
  have hseq (t : ℝ≥0) : Tendsto (fun n =>
      (finiteSum_memLp h2 (s n) t).toLp (finiteSum M (s n) t)) atTop
      (𝓝 (∑' i, (h2 i t).toLp (M i t))) := by
    simp_rw [heq]
    exact (hsum t).hasSum.comp hs
  obtain ⟨L, hpred, hLc, hlim⟩ :=
    MartingaleSquareMaximal.exists_global_predictable_continuous_L2_limit
      (fun n => finiteSum_martingale hM (s n))
      (fun n t => finiteSum_memLp h2 (s n) t)
      (fun n => finiteSum_ae_continuous hc (s n))
      (fun N => (hseq (N : ℝ≥0)).cauchySeq)
  choose hL2 hLlim using hlim
  have hLM : Martingale L F μ := MartingaleSquareMaximal.martingale_of_L2_limits
    (fun n => finiteSum_martingale hM (s n))
    (fun n t => finiteSum_memLp h2 (s n) t)
    hpred.stronglyAdapted hL2 hLlim
  have hHasSum (t : ℝ≥0) : HasSum (fun i => (h2 i t).toLp (M i t))
      ((hL2 t).toLp (L t)) := by
    have heq := tendsto_nhds_unique (hseq t) (hLlim t)
    rw [← heq]
    exact (hsum t).hasSum
  refine ⟨L, hL2, hpred, hLM, hLc, hHasSum, ?_⟩
  intro T
  have hterminal := PredictableL2.tendsto_integral_sq_error_of_hasSum
    (fun i => M i T) (fun i => h2 i T) (hL2 T) (hHasSum T)
  apply squeeze_zero
    (fun q => integral_nonneg (fun ω => ENNReal.toReal_nonneg))
    (fun q => ?_)
    (show Tendsto (fun q : Finset ι => 4 * ∫ ω,
      ((∑ i ∈ q, M i T ω) - L T ω) ^ 2 ∂μ) atTop (𝓝 0) from by
      simpa only [mul_zero] using hterminal.const_mul 4)
  have hbound := MartingaleStrongMaximal.integral_maximalSquare_le
    ((finiteSum_martingale hM q).sub hLM)
    (fun t => (finiteSum_memLp h2 q t).sub (hL2 t))
    (show ∀ᵐ ω ∂μ, Continuous (fun t => (finiteSum M q - L) t ω) from by
      filter_upwards [finiteSum_ae_continuous hc q, hLc] with ω hq hl
      exact hq.sub hl) T
  simpa only [Pi.sub_apply, finiteSum, MartingaleStrongMaximal.maximalSquare] using hbound

end Problem367.MartingaleSpatialLimit

end

end OAI
