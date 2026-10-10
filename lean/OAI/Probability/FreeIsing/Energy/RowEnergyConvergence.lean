import OAI.Probability.FreeIsing.Energy.EnergyLimit
import OAI.Probability.FreeIsing.Martingales.PredictableL2Completion

namespace OAI

noncomputable section

open Filter Finset
open scoped Topology

namespace Problem367.RowEnergyConvergence

theorem summable_limit_of_tsum_le
    {ι : Type*} {a : ℕ → ι → ℝ} {b : ι → ℝ} {K : ℝ}
    (ha : ∀ n i, 0 ≤ a n i) (hsum : ∀ n, Summable (a n))
    (hlim : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (b i)))
    (hbound : ∀ n, ∑' i, a n i ≤ K) :
    Summable b ∧ ∑' i, b i ≤ K := by
  classical
  have hb (i : ι) : 0 ≤ b i :=
    ge_of_tendsto (hlim i) (Eventually.of_forall fun n => ha n i)
  have hpartial (s : Finset ι) : ∑ i ∈ s, b i ≤ K := by
    apply le_of_tendsto (tendsto_finsetSum s fun i _ => hlim i)
    exact Eventually.of_forall fun n =>
      ((hsum n).sum_le_tsum s (fun i _ => ha n i)).trans (hbound n)
  have hs : Summable b := summable_of_sum_le hb hpartial
  exact ⟨hs, hs.tsum_le_of_sum_le hpartial⟩

theorem uniform_complement_tails_of_two_stage_bound
    {ι : Type*} {a : ℕ → ι → ℝ} {sets : ℕ → Finset ι}
    {early : ℕ → ℝ} {late : ℕ → ℕ → ℝ}
    (hsum : ∀ n, Summable (a n))
    (hearly : Tendsto early atTop (𝓝 0))
    (hlate : ∀ k, Tendsto (late k) atTop (𝓝 0))
    (hbound : ∀ n k L,
      (∑' i, a n i) - ∑ i ∈ sets L, a n i ≤ early k + late k L) :
    ∀ ε > 0, ∃ s : Finset ι,
      ∀ n, ∑' i : {i // i ∉ s}, a n i.1 ≤ ε := by
  intro ε hε
  obtain ⟨s, hs⟩ := Problem367.uniform_energy_tails_of_two_stage_bound
    hearly hlate hbound ε hε
  refine ⟨s, fun n => ?_⟩
  have hsplit := (hsum n).sum_add_tsum_subtype_compl s
  linarith [hs n]

theorem norm_sub_sq_le {H : Type*} [SeminormedAddCommGroup H] (x y : H) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hd := norm_nonneg (x - y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem tendsto_tsum_norm_sub_sq_of_uniform_tails
    {ι H : Type*} [NormedAddCommGroup H]
    {f : ℕ → ι → H} {g : ι → H} {K : ℝ}
    (hsum : ∀ n, Summable (fun i => ‖f n i‖ ^ 2))
    (hbound : ∀ n, ∑' i, ‖f n i‖ ^ 2 ≤ K)
    (hcoordinate : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i)))
    (htail : ∀ ε > 0, ∃ s : Finset ι,
      ∀ n, ∑' i : {i // i ∉ s}, ‖f n i.1‖ ^ 2 ≤ ε) :
    Summable (fun i => ‖g i‖ ^ 2) ∧
      (∀ n, Summable (fun i => ‖f n i - g i‖ ^ 2)) ∧
      Tendsto (fun n => ∑' i, ‖f n i - g i‖ ^ 2) atTop (𝓝 0) := by
  classical
  have henergy (i : ι) : Tendsto (fun n => ‖f n i‖ ^ 2) atTop
      (𝓝 (‖g i‖ ^ 2)) := (hcoordinate i).norm.pow 2
  have hg := (summable_limit_of_tsum_le (fun n i => sq_nonneg ‖f n i‖)
    hsum henergy hbound).1
  have herror (n : ℕ) : Summable (fun i => ‖f n i - g i‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => norm_sub_sq_le _ _)
      (((hsum n).mul_left 2).add (hg.mul_left 2))
  refine ⟨hg, herror, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro a ha
    exact Eventually.of_forall fun n =>
      ha.trans_le (tsum_nonneg fun i => sq_nonneg ‖f n i - g i‖)
  · intro ε hε
    obtain ⟨s, hs⟩ := htail (ε / 8) (by positivity)
    have hgtail : ∑' i : {i // i ∉ s}, ‖g i.1‖ ^ 2 ≤ ε / 8 :=
      (summable_limit_of_tsum_le
        (a := fun n (i : {i // i ∉ s}) => ‖f n i.1‖ ^ 2)
        (b := fun i : {i // i ∉ s} => ‖g i.1‖ ^ 2)
        (fun n i => sq_nonneg ‖f n i.1‖)
        (fun n => (hsum n).subtype (fun i => i ∉ s))
        (fun i => henergy i.1) hs).2
    have hfinite : Tendsto (fun n => ∑ i ∈ s, ‖f n i - g i‖ ^ 2)
        atTop (𝓝 0) := by
      have h := tendsto_finsetSum s (fun i _ =>
        (((hcoordinate i).sub_const (g i)).norm).pow 2)
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sum_const_zero]
        using h
    filter_upwards [(tendsto_order.1 hfinite).2 (ε / 2) (by positivity)] with n hn
    have herrtail : (∑' i : {i // i ∉ s}, ‖f n i.1 - g i.1‖ ^ 2) ≤
        2 * (∑' i : {i // i ∉ s}, ‖f n i.1‖ ^ 2) +
          2 * (∑' i : {i // i ∉ s}, ‖g i.1‖ ^ 2) := by
      calc
        _ ≤ ∑' i : {i // i ∉ s},
            (2 * ‖f n i.1‖ ^ 2 + 2 * ‖g i.1‖ ^ 2) :=
          Summable.tsum_le_tsum (fun i => norm_sub_sq_le _ _)
            ((herror n).subtype _)
            ((((hsum n).subtype _).mul_left 2).add ((hg.subtype _).mul_left 2))
        _ = _ := by
          simpa only [Function.comp_apply, tsum_mul_left] using
            ((((hsum n).subtype (fun i => i ∉ s)).mul_left 2).tsum_add
              ((hg.subtype (fun i => i ∉ s)).mul_left 2))
    rw [← (herror n).sum_add_tsum_subtype_compl s]
    linarith [hs n]

open MeasureTheory

theorem tendsto_tsum_integral_sq_sub_of_uniform_tails
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : ℕ → ι → Ω → ℝ} {g : ι → Ω → ℝ} {K : ℝ}
    (hf : ∀ n i, MemLp (f n i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hsum : ∀ n, Summable (fun i => ∫ ω, (f n i ω) ^ 2 ∂μ))
    (hbound : ∀ n, ∑' i, ∫ ω, (f n i ω) ^ 2 ∂μ ≤ K)
    (hcoordinate : ∀ i, Tendsto
      (fun n => ∫ ω, (f n i ω - g i ω) ^ 2 ∂μ) atTop (𝓝 0))
    (htail : ∀ ε > 0, ∃ s : Finset ι,
      ∀ n, ∑' i : {i // i ∉ s}, ∫ ω, (f n i.1 ω) ^ 2 ∂μ ≤ ε) :
    Summable (fun i => ∫ ω, (g i ω) ^ 2 ∂μ) ∧
      (∀ n, Summable (fun i => ∫ ω, (f n i ω - g i ω) ^ 2 ∂μ)) ∧
      Tendsto (fun n => ∑' i, ∫ ω, (f n i ω - g i ω) ^ 2 ∂μ)
        atTop (𝓝 0) := by
  let F : ℕ → ι → Lp ℝ 2 μ := fun n i => (hf n i).toLp (f n i)
  let G : ι → Lp ℝ 2 μ := fun i => (hg i).toLp (g i)
  have hF (n : ℕ) (i : ι) : ‖F n i‖ ^ 2 = ∫ ω, (f n i ω) ^ 2 ∂μ :=
    PredictableL2.norm_toLp_sq (hf n i)
  have hG (i : ι) : ‖G i‖ ^ 2 = ∫ ω, (g i ω) ^ 2 ∂μ :=
    PredictableL2.norm_toLp_sq (hg i)
  have hFG (n : ℕ) (i : ι) :
      ‖F n i - G i‖ ^ 2 = ∫ ω, (f n i ω - g i ω) ^ 2 ∂μ := by
    change ‖(hf n i).toLp (f n i) - (hg i).toLp (g i)‖ ^ 2 = _
    rw [← MemLp.toLp_sub]
    exact PredictableL2.norm_toLp_sq ((hf n i).sub (hg i))
  have hconv (i : ι) : Tendsto (fun n => F n i) atTop (𝓝 (G i)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have h : Tendsto (fun n => ‖F n i - G i‖ ^ 2) atTop (𝓝 0) := by
      simpa only [hFG] using hcoordinate i
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h.sqrt
  have h := tendsto_tsum_norm_sub_sq_of_uniform_tails
    (f := F) (g := G) (K := K)
    (fun n => by simpa only [hF] using hsum n)
    (fun n => by simpa only [hF] using hbound n) hconv
    (by simpa only [hF] using htail)
  simpa only [hG, hFG] using h

end Problem367.RowEnergyConvergence

end

end OAI
