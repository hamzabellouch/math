import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSchwartzInversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

/-! Exact symbols of finite dilated time-kernel sums. No bound or limit
on the number of scales is used in this identity. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def scaledTimeKernel (k : ℝ → ℂ) (l : ℝ) (t : ℝ) : ℂ :=
  (l⁻¹ : ℂ)*k (t/l)

theorem scaledTimeKernel_integrable (k : ℝ → ℂ) (hk : Integrable k)
    (l : ℝ) (hl : l≠0) : Integrable (scaledTimeKernel k l) := by
  have h := (hk.comp_mul_right' (inv_ne_zero hl)).const_mul (l⁻¹ : ℂ)
  apply h.congr
  filter_upwards [] with t
  change (l⁻¹ : ℂ)*k (t*l⁻¹)=scaledTimeKernel k l t
  rw [scaledTimeKernel, div_eq_mul_inv]

theorem scaledTimeKernel_fourier (k : ℝ → ℂ) (l : ℝ) (hl : 0<l) (omega : ℝ) :
    𝓕 (scaledTimeKernel k l) omega=𝓕 k (l*omega) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  simp only [Real.inner_apply, scaledTimeKernel, Circle.smul_def, smul_eq_mul]
  have hp (t : ℝ) : -(t*omega)=-((t/l)*(l*omega)) := by field_simp
  simp_rw [hp]
  calc
    _ = (l⁻¹ : ℂ)*∫ t, (Real.fourierChar (-((t/l)*(l*omega))) : ℂ)*k (t/l) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    _ = (l⁻¹ : ℂ)*(l • ∫ t, (Real.fourierChar (-(t*(l*omega))) : ℂ)*k t) := by
      rw [Measure.integral_comp_div (fun t => (Real.fourierChar (-(t*(l*omega))) : ℂ)*k t) l,
        abs_of_pos hl]
    _ = _ := by
      rw [Complex.real_smul, ← mul_assoc,
        inv_mul_cancel₀ (by exact_mod_cast hl.ne' : (l:ℂ)≠0), one_mul]

theorem band_integrand_integrable (psi : SchwartzMap ℝ ℂ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (scale slope : ℝ) (x : ℝ×ℝ) :
    Integrable (fun omega : ℝ×ℝ =>
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (psi (scale*(omega.1+slope*omega.2))*planarFourier f omega)) planeMeasure := by
  have hfreq : Continuous (fun omega : ℝ×ℝ => scale*(omega.1+slope*omega.2)) := by fun_prop
  have hphase : Continuous (fun omega : ℝ×ℝ => Real.fourierChar (x.1*omega.1+x.2*omega.2)) :=
    Real.continuous_fourierChar.comp (by fun_prop)
  have hc : Continuous (fun omega : ℝ×ℝ =>
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (psi (scale*(omega.1+slope*omega.2))*planarFourierSchwartz f omega)) :=
    hphase.smul ((psi.continuous.comp hfreq).mul (planarFourierSchwartz f).continuous)
  apply ((planarFourier_integrable f).norm.const_mul (SchwartzMap.seminorm ℝ 0 0 psi)).mono'
  · simpa only [planarFourierSchwartz_apply] using (hc.aestronglyMeasurable (μ := planeMeasure))
  · filter_upwards [] with omega
    rw [Circle.norm_smul, norm_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ psi _) (norm_nonneg _)

theorem finite_band_multiplier {ι : Type*} (I : Finset ι)
    (k : SchwartzMap ℝ ℂ) (len : ι → ℝ) (hlen : ∀ i∈I, 0<len i)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (u : ℝ×ℝ → ℝ) (x : ℝ×ℝ) :
    (∑ i∈I, slopeKernelOperator (scaledTimeKernel k (len i)) u f x) =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        ((∑ i∈I, 𝓕 k (len i*(omega.1+u x*omega.2)))*planarFourier f omega) ∂planeMeasure := by
  have hi (i : ι) := band_integrand_integrable (𝓕 k) f (len i) (u x) x
  have hterm (i : ι) (hiI : i∈I) :
      slopeKernelOperator (scaledTimeKernel k (len i)) u f x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (len i*(omega.1+u x*omega.2))*planarFourier f omega) ∂planeMeasure := by
    rw [schwartz_frozen_slope_multiplier _
      (scaledTimeKernel_integrable k k.integrable _ (hlen i hiI).ne'),
      funext (scaledTimeKernel_fourier k (len i) (hlen i hiI))]
    simp only [SchwartzMap.fourier_coe]
  calc
    _ = ∑ i∈I, ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (len i*(omega.1+u x*omega.2))*planarFourier f omega) ∂planeMeasure :=
      Finset.sum_congr rfl hterm
    _ = ∫ omega, ∑ i∈I, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (len i*(omega.1+u x*omega.2))*planarFourier f omega) ∂planeMeasure :=
      (integral_finsetSum I (fun i _ => hi i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with omega
      simp only [Finset.sum_mul, Finset.smul_sum]

end LipschitzHilbert.PacketRepresentation

end

end OAI
