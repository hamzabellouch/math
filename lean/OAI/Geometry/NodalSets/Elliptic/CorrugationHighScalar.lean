import OAI.Geometry.NodalSets.Elliptic.CorrugationFastLower

namespace OAI

namespace Yau.Geometry
noncomputable section

lemma corrugation_high_quadratic_lower {ν lp l r d δ u v w t : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hl : 0 ≤ l) (hr : 0 < r) (hr1 : r ≤ 1/4)
    (hd : 0 ≤ d) (hlp : -d ≤ lp) (hδ : 0 ≤ δ)
    (hu : |u| ≤ l+δ) (hv : |v| ≤ δ) (ht : 1/2 ≤ t)
    (hprod : l*d ≤ 1/16) (hloss : 3*d*δ^2 ≤ l/8) :
    l/2 ≤ ν*(lp*u*u+(l/r)*w*w)+(lp*v*v+(l/r)*t*t) := by
  have hu2 : u^2 ≤ (l+δ)^2 := (sq_abs u).symm.trans_le
    ((sq_le_sq₀ (abs_nonneg u) (add_nonneg hl hδ)).mpr hu)
  have hv2 : v^2 ≤ δ^2 := (sq_abs v).symm.trans_le ((sq_le_sq₀ (abs_nonneg v) hδ).mpr hv)
  have ht2 : (1:ℝ)/4 ≤ t^2 := by nlinarith
  have hu3 : u^2 ≤ 2*l^2+2*δ^2 := by nlinarith [sq_nonneg (l-δ)]
  have hνu := mul_le_mul_of_nonneg_right hν1 (sq_nonneg u)
  have hrad : ν*u^2+v^2 ≤ 2*l^2+3*δ^2 := by linarith
  have hrad0 : 0 ≤ ν*u^2+v^2 := by positivity
  have hradlp := mul_le_mul_of_nonneg_right hlp hrad0
  have hradd := mul_le_mul_of_nonneg_left hrad hd
  have hp := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hl)
  have hfrac : l ≤ (l/r)/4 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    apply (le_div_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hr1 hl]
  have hfrac0 : 0 ≤ l/r := div_nonneg hl hr.le
  have hang := mul_le_mul_of_nonneg_left ht2 hfrac0
  have hother : 0 ≤ ν*((l/r)*w^2) := by positivity
  nlinarith only [hl,hradlp,hradd,hp,hloss,hfrac,hang,hother]

end
end Yau.Geometry

end OAI
