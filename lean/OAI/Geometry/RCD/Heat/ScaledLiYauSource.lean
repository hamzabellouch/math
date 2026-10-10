import Mathlib

namespace OAI

/-! # A noise-dependent Li--Yau parameter controls the scaled source -/

namespace RegularPointCoordinates

theorem scaled_liYau_source_bound {c s δ N k g q : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ) (hδs : δ ≤ s)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hg : 0 ≤ g)
    (hLY : g ≤ (1+c)*(q+g)+
      (N*(1+c)^2/2)*(k/c+1/(c*s/4))) :
    -(c^2*g+2*N*k+8*N/δ) ≤ c*q := by
  have hs : 0 < s := hδ.trans_le hδs
  have hfrac := one_div_le_one_div_of_le hδ hδs
  have hcoef : N*(1+c)^2/2 ≤ 2*N := by
    have hp : (1+c)^2 ≤ 4 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hp hN
    linarith
  have ht : k+4/s ≤ k+4/δ := by
    apply add_le_add le_rfl
    simpa only [div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left hfrac (by norm_num : (0:ℝ) ≤ 4)
  have hC : c*((N*(1+c)^2/2)*(k/c+1/(c*s/4))) ≤ 2*N*k+8*N/δ := by
    calc
      _ = (N*(1+c)^2/2)*(k+4/s) := by field_simp
      _ ≤ (2*N)*(k+4/δ) := mul_le_mul hcoef
        ht (by positivity) (by positivity)
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hLY hc.le
  have hpos : 0 ≤ c^2*g+2*N*k+8*N/δ := by positivity
  by_contra hfail
  have hlt : c*q < -(c^2*g+2*N*k+8*N/δ) := lt_of_not_ge hfail
  have hneg : c*q < 0 := lt_of_lt_of_le hlt (neg_nonpos.mpr hpos)
  have hextra : c*(c*q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le hneg.le
  nlinarith

end RegularPointCoordinates

end OAI
