import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingFluxCoercivity

namespace OAI

/-! The total flux removes the last outgoing boundary channel. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralOutgoing_flux_limit (nu eps : ℕ → ℝ) (A : ℝ)
    (z w dz dw alpha : ℕ → ℂ)
    (heps : Tendsto eps atTop (𝓝 0))
    (hz : Tendsto (fun n => nu n*‖z n‖) atTop (𝓝 0))
    (hdz : Tendsto dz atTop (𝓝 0))
    (hflux : Tendsto (fun n => nu n*(spectralScalarFlux (z n,dz n)+spectralScalarFlux (w n,dw n)))
      atTop (𝓝 0))
    (hdata : ∀ᶠ n in atTop, 0 ≤ nu n ∧ 0 ≤ eps n ∧
      (alpha n).im ≤ -nu n/4 ∧ ‖alpha n‖ ≤ A*nu n ∧
      ‖dw n-alpha n*w n‖ ≤ eps n*nu n*(‖z n‖+‖w n‖)) :
    Tendsto (fun n => nu n*‖w n‖) atTop (𝓝 0) ∧ Tendsto dw atTop (𝓝 0) := by
  have hz' := tendsto_zero_iff_norm_tendsto_zero.mp hdz
  have hf : Tendsto (fun n => nu n*|spectralScalarFlux (z n,dz n)+spectralScalarFlux (w n,dw n)|)
      atTop (𝓝 0) := by
    have ha := continuous_abs.continuousAt.tendsto.comp hflux
    simp only [abs_zero] at ha
    apply ha.congr'
    filter_upwards [hdata] with n hn
    simp only [Function.comp_apply]
    rw [abs_mul,abs_of_nonneg hn.1]
  have hrhs : Tendsto (fun n => 8*(nu n*|spectralScalarFlux (z n,dz n)+spectralScalarFlux (w n,dw n)|+
      (nu n*‖z n‖)*‖dz n‖)+(nu n*‖z n‖)^2) atTop (𝓝 0) := by
    simpa using ((hf.add (hz.mul hz')).const_mul 8).add (hz.pow 2)
  have hs : Tendsto (fun n => (nu n*‖w n‖)^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => sq_nonneg _)) _ hrhs
    filter_upwards [hdata,heps.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/16))] with n hn hen
    exact spectralOutgoing_flux_coercivity _ _ _ _ _ _ _ hn.1 hn.2.1 hen.le hn.2.2.1 hn.2.2.2.2
  have hw : Tendsto (fun n => nu n*‖w n‖) atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simp only [Real.sqrt_zero] at ht
    apply ht.congr'
    filter_upwards [hdata] with n hn
    simp only [Function.comp_apply]
    rw [Real.sqrt_sq (mul_nonneg hn.1 (norm_nonneg _))]
  refine ⟨hw,?_⟩
  have hb : Tendsto (fun n => A*(nu n*‖w n‖)+eps n*(nu n*‖z n‖+nu n*‖w n‖)) atTop (𝓝 0) := by
    simpa using (hw.const_mul A).add (heps.mul (hz.add hw))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) _ hb
  filter_upwards [hdata] with n hn
  calc
    ‖dw n‖ ≤ ‖alpha n*w n‖+‖dw n-alpha n*w n‖ := norm_le_insert' _ _
    _ ≤ (A*nu n)*‖w n‖+eps n*nu n*(‖z n‖+‖w n‖) :=
      add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right hn.2.2.2.1 (norm_nonneg _)) hn.2.2.2.2
    _ = _ := by ring

end DefocusingNLS

end OAI
