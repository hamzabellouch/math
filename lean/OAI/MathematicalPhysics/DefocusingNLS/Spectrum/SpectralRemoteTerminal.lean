import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIncomingDecay

namespace OAI

/-! A vanishing terminal coordinate and an exponentially integrable derivative
give the quantitative incoming estimate. Qualitative decay removes the
solution-dependent endpoint before the uniform bound is applied. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem spectralRemote_terminal_bound (T alpha D : ℝ) (halpha : 0 < alpha)
    (g dg : ℝ → ℂ) (hdg : ContinuousOn dg (Ici T))
    (hderiv : ∀ t ∈ Ici T, HasDerivAt g (dg t) t)
    (hlim : Tendsto g atTop (𝓝 0))
    (hbound : ∀ t ∈ Ici T, ‖dg t‖ ≤ D*Real.exp (-alpha*t)) :
    ‖g T‖ ≤ D/alpha*Real.exp (-alpha*T) := by
  have hexp : IntegrableOn (fun t : ℝ => D*Real.exp (-alpha*t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos halpha) T).const_mul D
  have hmeas : AEStronglyMeasurable dg (volume.restrict (Ioi T)) :=
    (hdg.mono (Ioi_subset_Ici_self)).aestronglyMeasurable measurableSet_Ioi
  have hgi : IntegrableOn dg (Ioi T) := hexp.mono' hmeas (by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi T) measurableSet_Ioi] with t ht
    exact hbound t (mem_Ici.mpr (mem_Ioi.mp ht).le))
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hgi hlim
  calc
    ‖g T‖ = ‖∫ t in Ioi T, dg t‖ := by rw [hFTC,zero_sub,norm_neg]
    _ ≤ ∫ t in Ioi T, D*Real.exp (-alpha*t) := by
      apply norm_integral_le_of_norm_le hexp
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi T) measurableSet_Ioi] with t ht
      exact hbound t (mem_Ici.mpr (mem_Ioi.mp ht).le)
    _ = D/alpha*Real.exp (-alpha*T) := by
      rw [integral_const_mul,integral_exp_mul_Ioi (neg_neg_of_pos halpha)]
      ring

theorem spectralRemote_power_terminal_bound (T C m A M : ℝ) (hgap : 2*C < m)
    (g dg : ℝ → ℂ) (hdg : ContinuousOn dg (Ici T))
    (hderiv : ∀ t ∈ Ici T, HasDerivAt g (dg t) t)
    (hlim : Tendsto g atTop (𝓝 0))
    (hbound : ∀ t ∈ Ici T, ‖dg t‖ ≤
      A*M*Real.exp (-2*C*T)*Real.exp (-(m-2*C)*t)) :
    ‖g T‖ ≤ A*M/(m-2*C)*Real.exp (-m*T) := by
  have hb := spectralRemote_terminal_bound T (m-2*C) (A*M*Real.exp (-2*C*T))
    (sub_pos.mpr hgap) g dg hdg hderiv hlim hbound
  apply hb.trans_eq
  have he : Real.exp (-2*C*T)*Real.exp (-(m-2*C)*T) = Real.exp (-m*T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (A*M/(m-2*C))*(Real.exp (-2*C*T)*Real.exp (-(m-2*C)*T)) := by ring
    _ = _ := by rw [he]

end DefocusingNLS

end OAI
