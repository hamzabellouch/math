import OAI.Analysis.TriangularHilbert.RationalSup

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma norm_sampledIntegrand_le (B C : ℝ×ℝ → ℂ) {CB CC L : ℝ}
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC) (K : ℝ → ℝ)
    (hk : ∀ t, |K t| ≤ L) (h : ℝ) (z : ℝ×ℝ) (c : ℝ) :
    ‖sampledIntegrand B C h K z c‖ ≤ CB*CC*L := by
  unfold sampledIntegrand
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul (hb _) (hc _) (norm_nonneg _) ((norm_nonneg (B 0)).trans (hb 0)))
    (hk _) (abs_nonneg _) (mul_nonneg ((norm_nonneg (B 0)).trans (hb 0)) ((norm_nonneg (C 0)).trans (hc 0)))

lemma sampledIntegrand_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0))
    (K : ℝ → ℝ) (z : ℝ×ℝ) (c : ℝ) (hk : ContinuousAt K (z.1+z.2+c)) :
    Tendsto (fun n => sampledIntegrand B C (h n) K z c) atTop
      (𝓝 (B (z.2,c)*C (c,z.1)*(K (z.1+z.2+c):ℂ))) := by
  have ha := tendsto_gridPoint hh ht z.1
  have hb := tendsto_gridPoint hh ht z.2
  have hc := tendsto_gridPoint hh ht c
  exact (((hB.tendsto _).comp (hb.prodMk_nhds hc)).mul
    ((hC.tendsto _).comp (hc.prodMk_nhds ha))).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (hk.tendsto.comp ((ha.add hb).add hc)))

lemma sampledKernelOutput_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    (K : ℝ → ℝ) (hK : Measurable K) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ)
    (hcont : ∀ᵐ c : ℝ, ContinuousAt K (z.1+z.2+c)) :
    Tendsto (fun n => sampledKernelOutput B C (h n) K z) atTop (𝓝 (cyclicKernelOutput B C K z)) := by
  let b : ℝ → ℝ := (Set.Icc (-(M+1)) (M+1)).indicator (fun _ => CB*CC*L)
  apply tendsto_integral_of_dominated_convergence b
  · intro n
    exact ((measurable_sampledIntegrand B C hB.measurable hC.measurable (h n) K hK).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact (integrableOn_const (μ := volume) (s := Set.Icc (-(M+1)) (M+1)) (C := CB*CC*L)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  · intro n
    filter_upwards [] with c
    by_cases he : sampledIntegrand B C (h n) K z c = 0
    · rw [he,norm_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCB hCC) hL) _
    · have hmem : c ∈ Set.Icc (-(M+1)) (M+1) := abs_le.mp (sampledIntegrand_support_c B C (hh n) (hh1 n) hs K z c he)
      dsimp only [b]
      rw [Set.indicator_of_mem hmem]
      exact norm_sampledIntegrand_le B C hb hc K hk _ _ _
  · filter_upwards [hcont] with c hct
    exact sampledIntegrand_tendsto B C hB hC hh ht K z c hct

lemma ae_continuousAt_hardKernel (r R a : ℝ) : ∀ᵐ c : ℝ, ContinuousAt (hardKernel r R) (a+c) := by
  have hne (x : ℝ) : ∀ᵐ c : ℝ, c ≠ x := by simp [ae_iff]
  filter_upwards [hne (-a),hne (r-a),hne (-r-a),hne (R-a),hne (-R-a)] with c h0 h1 h2 h3 h4
  apply continuousAt_hardKernel
  · intro he; apply h0; linarith
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he with he|he
    · apply h1; linarith
    · apply h2; linarith
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he with he|he
    · apply h3; linarith
    · apply h4; linarith
end
end TriangularHilbert.Heat
end

end OAI
