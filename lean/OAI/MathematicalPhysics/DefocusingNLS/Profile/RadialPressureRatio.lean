import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAmplitudePotentialDerivative
import Mathlib.Algebra.Order.Ring.Pow

namespace OAI

/-! The pressure lower bound at a slope maximum sharpens the velocity ratio to O(1/m). -/

open Set
namespace DefocusingNLS

theorem radial_pressure_power_comparison (m : ℕ) (hm : 0 < m) (x y : ℝ)
    (hy : 0 < y) (hxP : x^(2*m) ≤ (1/2 : ℝ))
    (hyP : (1/5 : ℝ) ≤ y^(2*m)) :
    x^2 ≤ (1+3/(2*(m : ℝ)))*y^2 := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hy2 : 0 < y^2 := sq_pos_of_pos hy
  have hyp : 0 < (y^2)^m := pow_pos hy2 m
  have hp : (x^2/y^2)^m ≤ (5/2 : ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ hyp).2
    rw [← pow_mul,← pow_mul]
    nlinarith [hxP,hyP]
  have hq0 : -1 ≤ x^2/y^2 := le_trans (by norm_num)
    (div_nonneg (sq_nonneg x) hy2.le)
  have hb := one_add_mul_sub_le_pow hq0 m
  have hq : x^2/y^2 ≤ ((m : ℝ)+3/2)/(m : ℝ) :=
    (le_div_iff₀ hmR).2 (by nlinarith [hb,hp])
  have he : ((m : ℝ)+3/2)/(m : ℝ)=1+3/(2*(m : ℝ)) := by
    field_simp [hmR.ne']
  rw [he] at hq
  exact (div_le_iff₀ hy2).1 hq

theorem radialVelocityRatio_pressure_bound (m : ℕ) (hm : 0 < m)
    (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r) (A : ℝ → ℝ) (hA : Continuous A)
    (hAr : 0 < A r) (hP : ∀ t ∈ Icc 0 r, (A t)^(2*m) ≤ (1/2 : ℝ))
    (hPr : (1/5 : ℝ) ≤ (A r)^(2*m)) :
    radialVelocityRatio c A r ≤ c/12*(1+3/(2*(m : ℝ))) := by
  have hb := radialAverage_mono (fun t => (A t)^2)
    (fun _ => (1+3/(2*(m : ℝ)))*(A r)^2) (hA.pow 2) continuous_const r hr
    (fun t ht => radial_pressure_power_comparison m hm (A t) (A r) hAr (hP t ht) hPr)
  rw [radialAverage_const] at hb
  unfold radialVelocityRatio
  apply (div_le_iff₀ (sq_pos_of_pos hAr)).2
  calc
    c*radialAverage (fun t => (A t)^2) r ≤
        c*((1+3/(2*(m : ℝ)))*(A r)^2/12) := mul_le_mul_of_nonneg_left hb hc
    _ = c/12*(1+3/(2*(m : ℝ)))*(A r)^2 := by ring

theorem radial_pressure_potential_polynomial (a q : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hqlo : (49/100 : ℝ) ≤ q) (hqhi : q ≤ 1/2+3*a/4) :
    1/8-(6-a)/2*q+11/2*q^2 ≤ 6*a := by
  have hfactor : 0 ≤ 11/2*((1/2+3*a/4)+q)-(6-a)/2 := by linarith
  have hmono := mul_nonneg (sub_nonneg.mpr hqhi) hfactor
  have haa := mul_nonneg ha (sub_nonneg.mpr ha1)
  nlinarith

end DefocusingNLS

end OAI
