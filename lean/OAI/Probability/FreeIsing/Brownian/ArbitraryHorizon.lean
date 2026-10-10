import OAI.Probability.FreeIsing.Brownian.FiltrationUniformIntegral
import OAI.Probability.FreeIsing.Brownian.RationalHorizon
import OAI.Probability.FreeIsing.Brownian.UniformErrorContinuity
import OAI.Probability.FreeIsing.Estimates.MeanSquareContinuity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.BrownianArbitraryHorizon

lemma continuousOn_le_of_pos_rat {f : ℝ≥0 → ℝ} {N T : ℝ≥0} {c : ℝ}
    (hf : ContinuousOn f (Icc 0 N)) (hTN : T < N)
    (hrat : ∀ q : ℚ, 0 < q → (q : ℝ).toNNReal ≤ N →
      f (q : ℝ).toNNReal ≤ c) : f T ≤ c := by
  obtain ⟨q, _, hq, hlim⟩ := Real.exists_seq_rat_strictAnti_tendsto (T : ℝ)
  have hqp (n : ℕ) : 0 < q n := by
    have hr : (0 : ℝ) < q n := lt_of_le_of_lt T.coe_nonneg (hq n)
    exact_mod_cast hr
  have hl : Tendsto (fun n => (q n : ℝ).toNNReal) atTop (𝓝 T) := by
    simpa only [Function.comp_def, Real.toNNReal_coe] using (continuous_real_toNNReal.tendsto (T : ℝ)).comp hlim
  have he : ∀ᶠ n in atTop, (q n : ℝ).toNNReal ∈ Icc 0 N := by
    filter_upwards [hl.eventually (gt_mem_nhds hTN)] with n hn
    exact ⟨zero_le, hn.le⟩
  have hwithin := tendsto_nhdsWithin_iff.mpr ⟨hl, he⟩
  apply le_of_tendsto ((hf T ⟨zero_le, hTN.le⟩).tendsto.comp hwithin)
  filter_upwards [he] with n hn
  exact hrat (q n) (hqp n) hn.2

theorem uniformSum_tendsto_of_rat_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B H I : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H)
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hI2 : ∀ t, MemLp (I t) 2 P)
    (hcont : ∀ n N, ContinuousOn (fun T : ℝ≥0 => ∫ ω,
      (BrownianGrid.uniformSum B H T n ω - I T ω) ^ 2 ∂P) (Icc 0 N))
    (hrat : ∀ q : ℚ, 0 < q → Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H (q : ℝ).toNNReal n ω - I (q : ℝ).toNNReal ω)^2 ∂P)
        atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (BrownianGrid.uniformSum B H T n ω - I T ω)^2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P :=
    MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
      (hbH.mono (fun ω hω => hω t))
  have hS2 (t : ℝ≥0) (n : ℕ) : MemLp (BrownianGrid.uniformSum B H t n) 2 P :=
    BrownianFiltrationGrid.uniformSum_memLp hB hAd hind H hH hH2 t n
  let K : ℝ≥0 := T + 1
  have hTK : T < K := by dsimp [K]; exact lt_add_one T
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η : ℝ := ε / (8 * (K : ℝ) + 1)
  have hden : 0 < 8 * (K : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hmod⟩ := MeanSquareContinuity.uniform_integral_sq_sub_le
    (fun t => (hH2 t).aestronglyMeasurable) hcH hC hbH K hη
  obtain ⟨M, hM⟩ := exists_nat_gt ((K : ℝ) / δ)
  have hmesh (t : ℝ≥0) (ht : t ≤ K) (n : ℕ) (hn : M + 1 ≤ n) :
      (t : ℝ) / (n : ℝ) ≤ δ := by
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    apply (div_le_iff₀ hnR).mpr
    have hM' : (K : ℝ) < (M : ℝ) * δ := (div_lt_iff₀ hδ).mp hM
    have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show M ≤ n by omega)
    have ht' : (t : ℝ) ≤ K := ht
    nlinarith
  have hpair (t : ℝ≥0) (ht : t ≤ K) (n m : ℕ)
      (hn : M + 1 ≤ n) (hm : M + 1 ≤ m) :
      (∫ ω, (BrownianGrid.uniformSum B H t n ω -
        BrownianGrid.uniformSum B H t m ω)^2 ∂P) ≤ 4 * (K : ℝ) * η := by
    have hh := BrownianFiltrationGrid.preBrownian_uniform_pair_bound hB hAd hind H hH hH2 t
      (by omega : 0 < n) (by omega : 0 < m) (hmesh t ht n hn) (hmesh t ht m hm)
      (fun s r hsr hr hd => hmod s r hsr (hr.trans ht) hd)
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ K from ht) (by norm_num)) hη.le
  refine ⟨M + 1, ?_⟩
  intro n hn
  have hrbound (q : ℚ) (hq : 0 < q) (hqK : (q : ℝ).toNNReal ≤ K) :
      (∫ ω, (BrownianGrid.uniformSum B H (q : ℝ).toNNReal n ω -
        I (q : ℝ).toNNReal ω)^2 ∂P) ≤ 8 * (K : ℝ) * η := by
    have hlim : Tendsto (fun m => 8 * (K : ℝ) * η + 2 * ∫ ω,
        (BrownianGrid.uniformSum B H (q : ℝ).toNNReal m ω -
          I (q : ℝ).toNNReal ω)^2 ∂P) atTop (𝓝 (8 * (K : ℝ) * η)) := by
      simpa using tendsto_const_nhds.add ((hrat q hq).const_mul 2)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop (M + 1)] with m hm
    have htri := BrownianGrid.integral_sq_sub_le_two
      (hS2 (q : ℝ).toNNReal n) (hI2 (q : ℝ).toNNReal) (hS2 (q : ℝ).toNNReal m)
    have hp := hpair (q : ℝ).toNNReal hqK n m hn hm
    simp only [sub_sq_comm (I (q : ℝ).toNNReal _) (BrownianGrid.uniformSum B H (q : ℝ).toNNReal m _)] at htri
    linarith
  have hb := continuousOn_le_of_pos_rat (hcont n K) hTK hrbound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
  apply hb.trans_lt
  dsimp [η]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hden).mpr
  nlinarith

theorem uniformSum_tendsto_of_integer_stopped_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B H I : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hcB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hH : StronglyAdapted F H)
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hI : Martingale I F P) (hI2 : ∀ t, MemLp (I t) 2 P)
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hlim : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum B H N n t ω - I t ω)^2 ∂P)
        atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (BrownianGrid.uniformSum B H T n ω - I T ω)^2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hBM : Martingale B F P :=
    BrownianFiltration.martingale_of_independent_past hB hAd hind
  have hB2 (t : ℝ≥0) : MemLp (B t) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  apply uniformSum_tendsto_of_rat_limits hB hAd hind hH hcH hC hbH hI2
  · intro n N
    exact BrownianUniformErrorContinuity.continuousOn_uniformSum_meanSquare_error
      hBM hI hB2 hI2 hcB hcI hH hcH hC hbH n N
  · exact BrownianIntegralProcess.tendsto_uniformSum_pos_rat_of_integer_limits hlim

end Problem367.BrownianArbitraryHorizon

end

end OAI
