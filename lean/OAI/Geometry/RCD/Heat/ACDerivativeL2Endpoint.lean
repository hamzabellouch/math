import OAI.Geometry.RCD.Sobolev.ACDerivativeEndpointBound
import OAI.Geometry.RCD.Heat.HeatOffDiagonalL2

namespace OAI

/-! # Endpoint error from a square-integrable derivative residual -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem ac_endpoint_L2_error {f w E : ℝ → ℝ} {D : ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hw : IntegrableOn w (Icc (0:ℝ) 1))
    (hE : IntegrableOn E (Icc (0:ℝ) 1))
    (hbound : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 → (deriv f t-w t)^2 ≤ D^2*E t) :
    (f 1-f 0-(∫ t in Icc (0:ℝ) 1, w t))^2 ≤ D^2*(∫ t in Icc (0:ℝ) 1, E t) := by
  let ν := volume.restrict (Icc (0:ℝ) 1)
  let z t := deriv f t-w t
  have hdf : IntegrableOn (deriv f) (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hf.intervalIntegrable_deriv
  have hz : Integrable z ν := hdf.sub hw
  have hb : ∀ᵐ t ∂ν, (z t)^2 ≤ D^2*E t := by
    rw [show ν=volume.restrict (Ioo (0:ℝ) 1) by exact restrict_Ioo_eq_restrict_Icc.symm]
    filter_upwards [ae_restrict_of_ae hbound,ae_restrict_mem measurableSet_Ioo] with t ht hm
    exact ht hm
  have hsq : Integrable (fun t => (z t)^2) ν := by
    apply (hE.const_mul (D^2)).mono' (hz.aestronglyMeasurable.pow 2)
    filter_upwards [hb] with t ht
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (z t))] using ht
  have hL2 : MemLp z 2 ν := (memLp_two_iff_integrable_sq hz.aestronglyMeasurable).mpr hsq
  have hcs := integral_mul_sq_le_integral_sq ν z (fun _ => 1) hL2 (memLp_const (1:ℝ))
  have hmass : ν.real univ=1 := by simp [ν,Measure.real,Real.volume_Icc]
  have hcs' : (∫ t, z t ∂ν)^2 ≤ ∫ t, (z t)^2 ∂ν := by
    simpa only [mul_one,one_pow,integral_const,smul_eq_mul,hmass,sq_abs] using hcs
  have heq : (∫ t, z t ∂ν)=f 1-f 0-(∫ t in Icc (0:ℝ) 1, w t) := by
    rw [integral_sub hdf hw]
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one]
    rw [hf.integral_deriv_eq_sub]
  rw [heq] at hcs'
  exact hcs'.trans (by
    have hh := integral_mono_ae hsq (hE.const_mul (D^2)) hb
    simpa only [integral_const_mul] using hh)

end RegularPointCoordinates

end

end OAI
