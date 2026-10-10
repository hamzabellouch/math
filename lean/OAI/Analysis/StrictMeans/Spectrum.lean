import OAI.Analysis.StrictMeans.UniformMeans

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma integralMean_neg_one_pos (f : ℂ → ℂ) (hf : NormalizedUnivalent f)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : 0 < integralMean (-1) f r := by
  rw [integralMean_neg_one_as_family f hf hr0 hr]
  apply mul_pos (by positivity)
  apply intervalIntegral.integral_pos (by linarith [Real.pi_pos])
    (circleInverseDensity_continuous (normalizedDiskFamily f hf) hr0 hr).continuousOn
  · intro t _
    exact inv_nonneg.mpr (norm_nonneg _)
  · refine ⟨0,⟨by linarith [Real.pi_pos],Real.pi_pos.le⟩,?_⟩
    apply inv_pos.mpr
    apply norm_pos_iff.mpr
    exact diskFamily_derivative_ne_zero (normalizedDiskFamily f hf) ⟨_,circlePoint_mem_disk hr0 hr 0⟩

lemma boundary_log_inverse_tendsto :
    Tendsto (fun r : ℝ => Real.log (1/(1-r))) (𝓝[<] (1:ℝ)) atTop := by
  have hd : Tendsto (fun r : ℝ => 1-r) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self] using (tendsto_const_nhds.sub
        (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun r : ℝ => 1-r) (𝓝[<] (1:ℝ)) (𝓝 (1-1:ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < 1-r
      exact sub_pos.mpr hr
  simpa only [one_div,Function.comp_def] using Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hd)

lemma growthExponent_le_of_mean_bound (f : ℂ → ℂ) (hf : NormalizedUnivalent f)
    {C b : ℝ} (hC : 0 < C)
    (hbound : ∀ r : ℝ, 1/2 ≤ r → r < 1 → integralMean (-1) f r ≤ C*(1-r)^(-b)) :
    growthExponent (-1) f ≤ (b : EReal) := by
  have ht : Tendsto (fun r : ℝ => b+Real.log C / Real.log (1/(1-r)))
      (𝓝[<] (1:ℝ)) (𝓝 b) := by
    simpa using tendsto_const_nhds.add
      (Tendsto.div_atTop (tendsto_const_nhds (x := Real.log C)) boundary_log_inverse_tendsto)
  have hte : Tendsto (fun r : ℝ => ((b+Real.log C / Real.log (1/(1-r)) : ℝ) : EReal))
      (𝓝[<] (1:ℝ)) (𝓝 (b : EReal)) := (continuous_coe_real_ereal.tendsto b).comp ht
  have he : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ),
      ((Real.log (integralMean (-1) f r) / Real.log (1/(1-r)) : ℝ) : EReal) ≤
        ((b+Real.log C / Real.log (1/(1-r)) : ℝ) : EReal) := by
    have hrlo : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ), 1/2 ≤ r :=
      (eventually_ge_nhds (by norm_num : (1/2:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hrlo,self_mem_nhdsWithin] with r hr0 hr
    have hd : 0 < 1-r := sub_pos.mpr hr
    have hd1 : 1 < 1/(1-r) := (one_lt_div hd).mpr (by linarith)
    have hlogd : 0 < Real.log (1/(1-r)) := Real.log_pos hd1
    have hm := Real.log_le_log (integralMean_neg_one_pos f hf (by linarith) hr) (hbound r hr0 hr)
    rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hd _).ne',Real.log_rpow hd] at hm
    have hi : Real.log (1/(1-r)) = -Real.log (1-r) := by rw [one_div,Real.log_inv]
    apply EReal.coe_le_coe_iff.mpr
    apply (div_le_iff₀ hlogd).mpr
    have hc : (Real.log C / Real.log (1/(1-r)))*Real.log (1/(1-r)) = Real.log C :=
      div_mul_cancel₀ _ hlogd.ne'
    rw [add_mul,hc,hi]
    nlinarith
  exact (limsup_le_limsup he).trans_eq hte.limsup_eq

end
end StrictInverseFirstPower

end

end OAI
