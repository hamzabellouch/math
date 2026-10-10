import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! # Weighted directional bounds from a fixed quadratic density

The estimate keeps the small weighted directional energy separate from
its uniform bound. The dominating density may be merely integrable.
-/

open MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem weighted_directional_young {w D G H B M r : ℝ}
    (hw : 0 ≤ w) (hwB : w ≤ B) (hD : 0 ≤ D)
    (hG : 0 ≤ G) (hGM : G ≤ M) (hr : 0 < r)
    (hH : H^2 ≤ D*G^2) :
    4*r*(w*|H|) ≤ 4*r^2*B*D+M*(w*G) := by
  have hs : |H| ≤ Real.sqrt D*G := by
    apply (sq_le_sq₀ (abs_nonneg H) (mul_nonneg (Real.sqrt_nonneg D) hG)).mp
    simpa only [sq_abs,mul_pow,Real.sq_sqrt hD] using hH
  have hy : 4*r*(Real.sqrt D*G) ≤ 4*r^2*D+G^2 := by
    nlinarith [sq_nonneg (2*r*Real.sqrt D-G),Real.sq_sqrt hD]
  calc
    4*r*(w*|H|) ≤ w*(4*r*(Real.sqrt D*G)) := by
      nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg (by positivity : 0≤4*r) hw)]
    _ ≤ w*(4*r^2*D+G^2) := mul_le_mul_of_nonneg_left hy hw
    _ ≤ 4*r^2*B*D+M*(w*G) := by
      have h₁ := mul_le_mul_of_nonneg_right hwB (mul_nonneg (by positivity : 0≤4*r^2) hD)
      have h₂ := mul_le_mul_of_nonneg_left hGM (mul_nonneg hw hG)
      nlinarith

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem weighted_directional_integral_bound {w D G H : X → ℝ} {B M r : ℝ}
    (hr : 0 < r) (hD : Integrable D μ)
    (hE : Integrable (fun x => w x*G x) μ)
    (hH : Integrable (fun x => w x*|H x|) μ)
    (hb : ∀ᵐ x ∂μ, 0≤w x ∧ w x≤B ∧ 0≤D x ∧ 0≤G x ∧ G x≤M ∧ (H x)^2≤D x*(G x)^2) :
    4*r*(∫ x, w x*|H x| ∂μ) ≤
      4*r^2*B*(∫ x, D x ∂μ)+M*(∫ x, w x*G x ∂μ) := by
  have hi := integral_mono_ae (hH.const_mul (4*r))
    ((hD.const_mul (4*r^2*B)).add (hE.const_mul M))
    (hb.mono fun x hx => weighted_directional_young hx.1 hx.2.1 hx.2.2.1
      hx.2.2.2.1 hx.2.2.2.2.1 hr hx.2.2.2.2.2)
  have hadd := integral_add (hD.const_mul (4*r^2*B)) (hE.const_mul M)
  simp only [Pi.add_apply] at hi hadd
  rw [hadd,integral_const_mul,integral_const_mul,integral_const_mul] at hi
  exact hi

end RegularPointCoordinates

end

end OAI
