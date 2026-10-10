import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialEnergySpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! An annular integral representation of the outer radial trace. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_radial_trace_identity (R : ℝ) (hR : 0 < R)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ r ∈ Ioo (R/2) R, HasDerivAt f (g r) r) :
    (R/2 : ℝ) • f R=
      ∫ r in (R/2)..R, (f r+(r-R/2 : ℝ) • g r) := by
  let F := fun r : ℝ => (r-R/2 : ℝ) • f r
  have hc : Continuous F := (continuous_id.sub continuous_const).smul hf
  have hD (r : ℝ) (hr : r ∈ Ioo (R/2) R) :
      HasDerivAt F (f r+(r-R/2 : ℝ) • g r) r := by
    have h := ((hasDerivAt_id r).sub_const (R/2)).fun_smul (hfg r hr)
    simpa only [F,Pi.smul_apply,id_eq,one_smul,add_comm] using h
  have hsrc : Continuous (fun r => f r+(r-R/2 : ℝ) • g r) :=
    hf.add ((continuous_id.sub continuous_const).smul hg)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show R/2 ≤ R by linarith) hc.continuousOn hD (hsrc.intervalIntegrable _ _)
  have hhalf : R-R/2=R/2 := by ring
  simpa only [F,hhalf,sub_self,zero_smul,sub_zero] using he.symm

end DefocusingNLS

end OAI
