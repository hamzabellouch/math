import OAI.Geometry.RCD.Harmonic.WeightedDirectionalVanishing
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! # Mixed errors under bounded moving densities

The fixed integrable factor is separate from the small weighted energy.
This is the form needed for the mixed osmotic Hessian term.
-/

open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem weighted_mixed_young {w D E H B r : ℝ}
    (hw : 0 ≤ w) (hwB : w ≤ B) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hr : 0 < r) (hH : H^2 ≤ D*E) :
    4*r*(w*|H|) ≤ 4*r^2*B*D+w*E := by
  have hs : |H| ≤ Real.sqrt D*Real.sqrt E := by
    apply (sq_le_sq₀ (abs_nonneg H) (mul_nonneg (Real.sqrt_nonneg D) (Real.sqrt_nonneg E))).mp
    simpa only [sq_abs,mul_pow,Real.sq_sqrt hD,Real.sq_sqrt hE] using hH
  have hy : 4*r*|H| ≤ 4*r^2*D+E := by
    nlinarith [sq_nonneg (2*r*Real.sqrt D-Real.sqrt E),Real.sq_sqrt hD,Real.sq_sqrt hE,
      mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*r by positivity)]
  have hwy := mul_le_mul_of_nonneg_left hy hw
  have hwb := mul_le_mul_of_nonneg_right hwB (mul_nonneg (show 0 ≤ 4*r^2 by positivity) hD)
  nlinarith only [hwy,hwb]

variable {X Y : Type*} [MeasurableSpace X] (μ : Measure X)

theorem weighted_mixed_error_vanishes
    (W E H : ℕ → Y → X → ℝ) (D : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hD : Integrable D μ) (hD0 : ∀ᵐ x ∂μ, 0 ≤ D x)
    (hEi : ∀ k y, Integrable (fun x => W k y x*E k y x) μ)
    (hHi : ∀ k y, Integrable (fun x => W k y x*|H k y x|) μ)
    (hpoint : ∀ k y, ∀ᵐ x ∂μ, 0 ≤ W k y x ∧ W k y x ≤ B ∧
      0 ≤ E k y x ∧ (H k y x)^2 ≤ D x*E k y x)
    (hlim : TendstoUniformly (fun k y => ∫ x, W k y x*E k y x ∂μ) (fun _ => 0) atTop) :
    TendstoUniformly (fun k y => ∫ x, W k y x*|H k y x| ∂μ) (fun _ => 0) atTop := by
  apply tendstoUniformly_of_directional_bound
    (C := B*(∫ x, D x ∂μ)) (M := 1)
    (mul_nonneg hB (integral_nonneg_of_ae hD0)) (by norm_num)
    (fun k y => integral_nonneg_of_ae ((hpoint k y).mono fun x hx => mul_nonneg hx.1 (abs_nonneg _))) hlim
  intro k y r hr
  have hi := integral_mono_ae ((hHi k y).const_mul (4*r))
    ((hD.const_mul (4*r^2*B)).add (hEi k y))
    (by
      filter_upwards [hpoint k y,hD0] with x hx hd
      exact weighted_mixed_young hx.1 hx.2.1 hd hx.2.2.1 hr hx.2.2.2)
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (hD.const_mul (4*r^2*B)) (hEi k y),integral_const_mul] at hi
  nlinarith only [hi]

end RegularPointCoordinates

end

end OAI
