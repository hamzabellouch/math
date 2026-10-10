import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnWeight

namespace OAI

/-! The full boundary and coupling error tends to zero as the remote
radius and the common scalar weight floor escape to infinity. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralBoundaryError_tendsto (E kap : ℕ → ℝ)
    (hE : Tendsto E atTop atTop) (hkap : Tendsto kap atTop atTop)
    (A B C R : ℝ) :
    Tendsto (fun n => (A+1)*(B/E n+C/R)/(kap n)^2) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => B/E n+C/R) atTop (𝓝 (C/R)) := by
    simpa only [mul_zero,zero_add,div_eq_mul_inv,Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp hE).const_mul B).add_const (C/R)
  have hk : Tendsto (fun n => ((kap n)^2)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,inv_pow,zero_pow (by norm_num : 2 ≠ 0)] using
      (tendsto_inv_atTop_zero.comp hkap).pow 2
  simpa only [div_eq_mul_inv,mul_zero] using (hb.const_mul (A+1)).mul hk

end DefocusingNLS

end OAI
