import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The two-channel perturbation has small Green norm when the scalar shell
frequencies are large. The coefficient decay is exactly the exterior r⁻² decay. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralShellPairNorm (kp km : ℝ) (u : (ℂ × ℂ) × (ℂ × ℂ)) : ℝ :=
  max (spectralShellNorm kp u.1) (spectralShellNorm km u.2)

theorem spectralShellPairNorm_nonneg (kp km : ℝ) (hkp : 0≤ kp)
    (u : (ℂ × ℂ) × (ℂ × ℂ)) : 0≤ spectralShellPairNorm kp km u :=
  (spectralShellNorm_nonneg kp hkp u.1).trans (le_max_left _ _)

theorem spectralShellPairNorm_values (kp km k : ℝ) (hk : 0<k)
    (hkp : k≤ kp) (hkm : k≤ km) (u : (ℂ × ℂ) × (ℂ × ℂ)) :
    ‖u.1.1‖≤ spectralShellPairNorm kp km u/k ∧
      ‖u.2.1‖≤ spectralShellPairNorm kp km u/k := by
  have hp := (spectralShellNorm_value kp (hk.trans_le hkp) u.1)
  have hm := (spectralShellNorm_value km (hk.trans_le hkm) u.2)
  constructor
  · apply hp.trans
    exact div_le_div₀ (spectralShellPairNorm_nonneg kp km (hk.trans_le hkp).le u)
      (le_max_left _ _) hk hkp
  · apply hm.trans
    exact div_le_div₀ (spectralShellPairNorm_nonneg kp km (hk.trans_le hkp).le u)
      (le_max_right _ _) hk hkm

theorem spectralShellCoupling_norm (kp km k C r : ℝ)
    (hk : 0<k) (hkp : k≤ kp) (hkm : k≤ km) (hC : 0≤ C)
    (u : (ℂ × ℂ) × (ℂ × ℂ)) (a b : ℂ)
    (ha : ‖a‖≤ C/r^2) (hb : ‖b‖≤ C/r^2) :
    ‖a*u.1.1+b*u.2.1‖≤(2*C/(k*r^2))*spectralShellPairNorm kp km u := by
  obtain ⟨hp,hm⟩ := spectralShellPairNorm_values kp km k hk hkp hkm u
  have hN := spectralShellPairNorm_nonneg kp km (hk.trans_le hkp).le u
  calc
    _ ≤ ‖a*u.1.1‖+‖b*u.2.1‖ := norm_add_le _ _
    _ = ‖a‖*‖u.1.1‖+‖b‖*‖u.2.1‖ := by rw [norm_mul,norm_mul]
    _ ≤ (C/r^2)*(spectralShellPairNorm kp km u/k)+
        (C/r^2)*(spectralShellPairNorm kp km u/k) := by gcongr
    _ = _ := by ring

theorem spectral_inverse_square_integral (R E : ℝ) (hR : 0<R) (hRE : R≤ E) :
    (∫ t in R..E, (t^2)⁻¹)=R⁻¹-E⁻¹ := by
  have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Icc R E) :=
    continuousOn_id.inv₀ (fun t ht => ne_of_gt (hR.trans_le ht.1))
  have hi : IntervalIntegrable (fun t : ℝ => -(t^2)⁻¹) volume R E := by
    apply ContinuousOn.intervalIntegrable_of_Icc hRE
    exact (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (ne_of_gt (hR.trans_le ht.1))) |>.neg
  have hd (t : ℝ) (ht : t ∈ Ioo R E) : HasDerivAt (fun x : ℝ => x⁻¹) (-(t^2)⁻¹) t := by
    convert! (hasDerivAt_id t).inv (ne_of_gt (hR.trans ht.1)) using 1
    simp only [id_eq,neg_div,one_div]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hRE hc hd hi
  rw [intervalIntegral.integral_neg] at he
  linarith

theorem spectral_inverse_square_integral_le (R E : ℝ) (hR : 0<R) (hRE : R≤ E) :
    (∫ t in R..E, (t^2)⁻¹)≤ R⁻¹ := by
  rw [spectral_inverse_square_integral R E hR hRE]
  exact sub_le_self _ (inv_nonneg.mpr (hR.trans_le hRE).le)

end DefocusingNLS

end OAI
