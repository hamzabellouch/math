import OAI.Probability.FreeIsing.Martingales.SpatialLimit
import OAI.Probability.FreeIsing.Stochastic.IntegralAssociativityLimit

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.MartingaleIntegerIdentification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : Filtration ℝ≥0 mΩ}

theorem ae_eq_of_positive_integer
    {X Y : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X F μ) (hY : Martingale Y F μ)
    (he : ∀ N : ℕ, 0 < N → X N =ᵐ[μ] Y N) (t : ℝ≥0) :
    X t =ᵐ[μ] Y t := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hN0 : 0 < N := by
    have hn : (0 : ℝ≥0) < (N : ℝ≥0) := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ t from zero_le) hN
    exact_mod_cast hn
  exact (hX.condExp_ae_eq hN.le).symm.trans
    ((condExp_congr_ae (he N hN0)).trans (hY.condExp_ae_eq hN.le))

theorem meanSquare_limit_of_positive_integer [IsFiniteMeasure μ]
    {α : Type*} {l : Filter α} {X : α → ℝ≥0 → Ω → ℝ}
    {Y : ℝ≥0 → Ω → ℝ}
    (hX : ∀ a, Martingale (X a) F μ) (hY : Martingale Y F μ)
    (hX2 : ∀ a t, MemLp (X a t) 2 μ) (hY2 : ∀ t, MemLp (Y t) 2 μ)
    (hlim : ∀ N : ℕ, 0 < N → Tendsto (fun a =>
      ∫ ω, (X a N ω - Y N ω) ^ 2 ∂μ) l (𝓝 0)) (t : ℝ≥0) :
    Tendsto (fun a => ∫ ω, (X a t ω - Y t ω) ^ 2 ∂μ) l (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hN0 : 0 < N := by
    have hn : (0 : ℝ≥0) < (N : ℝ≥0) := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ t from zero_le) hN
    exact_mod_cast hn
  apply squeeze_zero (fun a => integral_nonneg (fun ω => sq_nonneg _))
    (fun a => ?_) (hlim N hN0)
  exact MartingaleSquareMaximal.integral_sq_le ((hX a).sub hY)
    (fun s => (hX2 a s).sub (hY2 s)) hN.le

theorem finiteSum_meanSquare_of_positive_integer [IsFiniteMeasure μ]
    {ι : Type*} {M : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (hY : Martingale Y F μ)
    (hM2 : ∀ i t, MemLp (M i t) 2 μ) (hY2 : ∀ t, MemLp (Y t) 2 μ)
    (hlim : ∀ N : ℕ, 0 < N → Tendsto (fun s : Finset ι =>
      ∫ ω, ((∑ i ∈ s, M i N ω) - Y N ω) ^ 2 ∂μ) atTop (𝓝 0))
    (t : ℝ≥0) :
    Tendsto (fun s : Finset ι =>
      ∫ ω, ((∑ i ∈ s, M i t ω) - Y t ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  exact meanSquare_limit_of_positive_integer
    (fun s => MartingaleSpatialLimit.finiteSum_martingale hM s) hY
    (fun s t => MartingaleSpatialLimit.finiteSum_memLp hM2 s t) hY2 hlim t

theorem hasSum_of_positive_integer [IsFiniteMeasure μ]
    {ι : Type*} {M : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (hY : Martingale Y F μ)
    (hM2 : ∀ i t, MemLp (M i t) 2 μ) (hY2 : ∀ t, MemLp (Y t) 2 μ)
    (hlim : ∀ N : ℕ, 0 < N → Tendsto (fun s : Finset ι =>
      ∫ ω, ((∑ i ∈ s, M i N ω) - Y N ω) ^ 2 ∂μ) atTop (𝓝 0))
    (t : ℝ≥0) :
    HasSum (fun i => (hM2 i t).toLp (M i t)) ((hY2 t).toLp (Y t)) := by
  have hh := (SimpleIntegral.tendsto_toLp_iff_meanSquare
    (fun s => MartingaleSpatialLimit.finiteSum_memLp hM2 s t) (hY2 t)).mpr
      (finiteSum_meanSquare_of_positive_integer hM hY hM2 hY2 hlim t)
  have he (s : Finset ι) :
      (MartingaleSpatialLimit.finiteSum_memLp hM2 s t).toLp
        (MartingaleSpatialLimit.finiteSum M s t) =
        ∑ i ∈ s, (hM2 i t).toLp (M i t) :=
    PredictableL2.toLp_finsetSum (fun i => M i t) (fun i => hM2 i t) s
  change Tendsto (fun s : Finset ι => ∑ i ∈ s, (hM2 i t).toLp (M i t))
    atTop (𝓝 ((hY2 t).toLp (Y t)))
  simpa only [he] using hh

theorem finiteSum_maximalSquare_of_positive_integer [IsFiniteMeasure μ]
    {ι : Type*} {M : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (hY : Martingale Y F μ)
    (hM2 : ∀ i t, MemLp (M i t) 2 μ) (hY2 : ∀ t, MemLp (Y t) 2 μ)
    (hcM : ∀ i, ∀ᵐ ω ∂μ, Continuous (fun t => M i t ω))
    (hcY : ∀ᵐ ω ∂μ, Continuous (fun t => Y t ω))
    (hlim : ∀ N : ℕ, 0 < N → Tendsto (fun s : Finset ι =>
      ∫ ω, ((∑ i ∈ s, M i N ω) - Y N ω) ^ 2 ∂μ) atTop (𝓝 0))
    (T : ℝ≥0) :
    Tendsto (fun s : Finset ι => ∫ ω,
      MartingaleStrongMaximal.maximalSquare
        (MartingaleSpatialLimit.finiteSum M s - Y) T ω ∂μ) atTop (𝓝 0) := by
  have ht := finiteSum_meanSquare_of_positive_integer hM hY hM2 hY2 hlim T
  apply squeeze_zero
    (fun s => integral_nonneg (fun ω => ENNReal.toReal_nonneg))
    (fun s => ?_)
    (show Tendsto (fun s : Finset ι => 4 * ∫ ω,
      ((∑ i ∈ s, M i T ω) - Y T ω) ^ 2 ∂μ) atTop (𝓝 0) from by
      simpa only [mul_zero] using ht.const_mul 4)
  have hc : ∀ᵐ ω ∂μ,
      Continuous (fun t => (MartingaleSpatialLimit.finiteSum M s - Y) t ω) := by
    filter_upwards [MartingaleSpatialLimit.finiteSum_ae_continuous hcM s, hcY]
      with ω hm hy
    exact hm.sub hy
  exact MartingaleStrongMaximal.integral_maximalSquare_le
    ((MartingaleSpatialLimit.finiteSum_martingale hM s).sub hY)
    (fun t => (MartingaleSpatialLimit.finiteSum_memLp hM2 s t).sub (hY2 t)) hc T

end Problem367.MartingaleIntegerIdentification

end

end OAI
