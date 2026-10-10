import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningErrorLimit

namespace OAI

/-! Choose one finite turning cutoff before passing to the escaping
parameter sequence. All constants are fixed independently of that sequence. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralTurning_cutoff_choice (K L H c : ℝ) (hc : 0 < c)
    (r₀ d E : ℕ → ℝ) (hr₀ : Tendsto r₀ atTop atTop)
    (hd : Tendsto d atTop (𝓝 0)) (hE : Tendsto E atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ r₀ n ∧ 0 ≤ d n) :
    ∃ M : ℝ, 32 ≤ M ∧ ∀ᶠ n in atTop,
      0 ≤ spectralTurningOuterError M (r₀ n) (d n) ∧
      spectralTurningOuterError M (r₀ n) (d n) ≤ 1 ∧
      c/2 ≤ c-(K*spectralTurningOuterError M (r₀ n) (d n)+L/(E n)^2)*
        (H+(K*spectralTurningOuterError M (r₀ n) (d n)+L/(E n)^2)) := by
  have hj := spectralTurningCutoffError_tendsto
  have hcst : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hHst : Tendsto (fun _ : ℝ => H) atTop (𝓝 H) := tendsto_const_nhds
  have hlim := hcst.sub ((hj.const_mul K).mul (hHst.add (hj.const_mul K)))
  have hsmall : ∀ᶠ M : ℝ in atTop,
      spectralTurningCutoffError M < 1 ∧
      c/2 < c-(K*spectralTurningCutoffError M)*(H+K*spectralTurningCutoffError M) := by
    have hhalf : c/2 < c := by linarith
    have hlim' : Tendsto (fun M : ℝ => c-(K*spectralTurningCutoffError M)*
        (H+K*spectralTurningCutoffError M)) atTop (𝓝 c) := by
      simpa only [mul_zero,add_zero,zero_mul,sub_zero] using hlim
    exact (hj.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).and
      (hlim'.eventually (lt_mem_nhds hhalf))
  obtain ⟨M,hM,hm⟩ := ((eventually_ge_atTop (32 : ℝ)).and hsmall).exists
  refine ⟨M,hM,?_⟩
  have hJ := spectralTurningOuterError_tendsto M r₀ d hr₀ hd
  have hi := tendsto_inv_atTop_zero.comp hE
  have hrm : Tendsto (fun n => L/(E n)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,inv_pow,Function.comp_def,mul_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]
      using (hi.pow 2).const_mul L
  have hDel := (hJ.const_mul K).add hrm
  have hcseq : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hHseq : Tendsto (fun _ : ℕ => H) atTop (𝓝 H) := tendsto_const_nhds
  have hf := hcseq.sub (hDel.mul (hHseq.add hDel))
  have hf' : Tendsto (fun n => c-(K*spectralTurningOuterError M (r₀ n) (d n)+L/(E n)^2)*
      (H+(K*spectralTurningOuterError M (r₀ n) (d n)+L/(E n)^2))) atTop
      (𝓝 (c-(K*spectralTurningCutoffError M)*(H+K*spectralTurningCutoffError M))) := by
    simpa only [add_zero] using hf
  filter_upwards [hdata,hJ.eventually (gt_mem_nhds hm.1),hf'.eventually (lt_mem_nhds hm.2)]
    with n hn hjn hfn
  refine ⟨?_,hjn.le,hfn.le⟩
  rcases hn with ⟨hrn,hdn⟩
  dsimp only [spectralTurningOuterError,spectralTurningCutoffError]
  positivity

end DefocusingNLS

end OAI
