import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialRepresentative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialPrimitiveEvaluation

namespace OAI

/-! The completed radial H¹ bound excludes the singular harmonic branch at the origin. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralRadialRepresentative_origin_decay (R : ℝ) (hR : 0 < R)
    (u : SpectralRadialEnergy R) (ell : ℕ) :
    Tendsto (fun r : ℝ => (r : ℂ)^(ell+10)*spectralRadialRepresentative R hR u r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let T := ‖spectralRadialTrace R hR u‖
  let D := ‖spectralRadialDerivative R u‖
  have hb (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
      ‖(r : ℂ)^(ell+10)*spectralRadialRepresentative R hR u r‖ ≤
        r^(ell+10)*T+r^(ell+5)*D := by
    have hd := spectralRadialPointValue_difference_bound R hR r hr hrR u
    let d := ‖spectralRadialPointValue R hR r hr u-spectralRadialTrace R hR u‖
    have hd' : (r^5*d)^2 ≤ D^2 := by
      calc
        (r^5*d)^2 = r^10*d^2 := by ring
        _ ≤ r^10*(((r^10)⁻¹/10)*D^2) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
        _ = D^2/10 := by field_simp
        _ ≤ D^2 := by nlinarith [sq_nonneg D]
    have hrd : r^5*d ≤ D := by
      have hD : 0 ≤ D := norm_nonneg _
      nlinarith [sq_nonneg (r^5*d-D)]
    have htri : ‖spectralRadialPointValue R hR r hr u‖ ≤ T+d := by
      simpa only [T,d,norm_sub_rev] using
        norm_le_norm_add_norm_sub (spectralRadialTrace R hR u)
          (spectralRadialPointValue R hR r hr u)
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
      spectralRadialRepresentative,dite_eq_left hr]
    calc
      _ ≤ r^(ell+10)*(T+d) := mul_le_mul_of_nonneg_left htri (by positivity)
      _ = r^(ell+10)*T+r^(ell+5)*(r^5*d) := by
        rw [show ell+10=ell+5+5 by omega,pow_add]
        ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hrd (by positivity))
  apply squeeze_zero_norm' (a := fun r : ℝ => r^(ell+10)*T+r^(ell+5)*D) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with r hr hrR
    exact hb r hr hrR.le
  · have ht : Tendsto (fun r : ℝ => r^(ell+10)*T+r^(ell+5)*D)
        (𝓝 (0 : ℝ)) (𝓝 (0^(ell+10)*T+0^(ell+5)*D)) :=
      (show Continuous (fun r : ℝ => r^(ell+10)*T+r^(ell+5)*D) by fun_prop).tendsto 0
    simpa using ht.mono_left nhdsWithin_le_nhds

end DefocusingNLS

end OAI
