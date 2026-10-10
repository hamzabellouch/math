import OAI.Probability.InvariantIsing.Fields.SpinCoverError

namespace OAI

/-! The geometric and fiber-count costs of a fine spin cover can both be made small. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma exists_small_spinCover_error (K C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ δ t : ℝ, 0<δ ∧ 0≤t ∧
      2*K*Real.sqrt δ+(2*C+t)*δ+Real.log (1+Real.exp (-t))<ε := by
  have he : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun n : ℕ => Real.log (1+Real.exp (-(n:ℝ)))) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => 1+Real.exp (-(n:ℝ))) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).add he
    simpa only [Function.comp_def,Real.log_one] using (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hh
  obtain ⟨n,hn⟩ := (hl.eventually (Iio_mem_nhds (half_pos hε))).exists
  have hd := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hf : Tendsto (fun j : ℕ => 2*K*Real.sqrt (1/(j+1:ℝ))+
      (2*C+(n:ℝ))*(1/(j+1:ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ((Real.continuous_sqrt.tendsto 0 |>.comp hd).const_mul (2*K)).add
      (hd.const_mul (2*C+(n:ℝ)))
  obtain ⟨j,hj⟩ := (hf.eventually (Iio_mem_nhds (half_pos hε))).exists
  exact ⟨1/(j+1:ℝ),(n:ℝ),by positivity,Nat.cast_nonneg n,by linarith⟩

end InvariantIsing

end

end OAI
