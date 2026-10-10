import OAI.Analysis.TriangularHilbert.FiniteMoment

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

def outputBound (M CB CC L : ℝ) : ℝ := ∫ c : ℝ,
  (Set.Icc (-(M+1)) (M+1)).indicator (fun _ => CB*CC*L) c

lemma outputBound_nonneg (M : ℝ) {CB CC L : ℝ} (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L) :
    0 ≤ outputBound M CB CC L :=
  integral_nonneg (fun c => Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCB hCC) hL) c)

lemma sampledKernelOutput_bound (B C : ℝ×ℝ → ℂ) {M CB CC L h : ℝ}
    (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC) (hh : 0 < h) (hh1 : h ≤ 1)
    (K : ℝ → ℝ) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ) :
    ‖sampledKernelOutput B C h K z‖ ≤ outputBound M CB CC L := by
  apply norm_integral_le_of_norm_le
    ((integrableOn_const (μ := volume) (s := Set.Icc (-(M+1)) (M+1)) (C := CB*CC*L)
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc)
  filter_upwards [] with c
  by_cases he : sampledIntegrand B C h K z c = 0
  · rw [he,norm_zero]
    exact Set.indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hCB hCC) hL) c
  · rw [Set.indicator_of_mem (show c ∈ Set.Icc (-(M+1)) (M+1) from
      abs_le.mp (sampledIntegrand_support_c B C hh hh1 hs K z c he))]
    exact norm_sampledIntegrand_le B C hb hc K hk _ _ _

lemma sampled_moment_tendsto (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ)
    (hK : ∀ k, Measurable (K k)) (hk : ∀ k t, |K k t| ≤ L)
    (hcont : ∀ k (z : ℝ×ℝ), ∀ᵐ c : ℝ, ContinuousAt (K k) (z.1+z.2+c)) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C (h n) (K k) z)) atTop
      (𝓝 (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (K k) z))) := by
  let T := outputBound M CB CC L
  have hT : 0 ≤ T := outputBound_nonneg M hCB hCC hL
  let b : ℝ×ℝ → ℝ := (closedBox (M+1)).indicator (fun _ => T*Real.sqrt T)
  apply tendsto_integral_of_dominated_convergence b
  · intro n
    exact (continuous_finiteMoment.measurable.comp (Measurable.of_eval
      (fun k => measurable_sampledKernelOutput B C hB.measurable hC.measurable (h n) (K k) (hK k)))).aestronglyMeasurable
  · exact (integrableOn_const (μ := volume) (s := closedBox (M+1)) (C := T*Real.sqrt T)
      (volume_closedBox_ne_top _)).integrable_indicator (measurableSet_closedBox _)
  · intro n
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (finiteMoment_nonneg _)]
    by_cases hz : z ∈ closedBox (M+1)
    · dsimp only [b]
      rw [Set.indicator_of_mem hz]
      exact finiteMoment_le _ (fun k => sampledKernelOutput_bound B C hsB hCB hCC hL hb hc (hh n) (hh1 n) (K k) (hk k) z)
    · have he : (fun k => sampledKernelOutput B C (h n) (K k) z) = fun _ : κ => (0:ℂ) :=
        funext (fun k => sampledKernelOutput_support B C (hh n) (hh1 n) hsB hsC (K k) z hz)
      rw [he,finiteMoment_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hT (Real.sqrt_nonneg _)) z
  · filter_upwards [] with z
    apply continuous_finiteMoment.continuousAt.tendsto.comp
    exact tendsto_pi_nhds.mpr (fun k => sampledKernelOutput_tendsto B C hB hC hsB hCB hCC hL hb hc
      hh hh1 ht (K k) (hK k) (hk k) z (hcont k z))
end
end TriangularHilbert.Heat
end

end OAI
