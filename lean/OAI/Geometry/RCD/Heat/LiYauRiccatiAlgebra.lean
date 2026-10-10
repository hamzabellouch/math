import Mathlib.Tactic

namespace OAI

/-! # The scalar reduction for the parameter-two Li--Yau estimate -/

namespace RegularPointCoordinates

theorem liYau_riccati_algebra {n M k I D rate : ℝ}
    (hn : 0<n) (hM : 0<M) (hk : 0≤k) (hI : 0≤I)
    (hbound : (2/n)*(D-I)^2-2*k*M*I≤M*rate)
    (hthreshold : 2*n*M*k≤I-2*D) :
    (1/(2*n*M))*(I-2*D-2*n*M*k)^2≤rate := by
  have hm := mul_le_mul_of_nonneg_left hbound hn.le
  have he : n*((2/n)*(D-I)^2-2*k*M*I)=2*(D-I)^2-2*k*n*M*I := by
    field_simp
  rw [he] at hm
  have hcross := mul_nonneg hI (sub_nonneg.mpr hthreshold)
  have hr : 0≤2*n*M*k := by positivity
  have hsq : (I-2*D-2*n*M*k)^2≤(I-2*D)^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hthreshold) (sub_le_self _ hr) 2
  have hfinal : (I-2*D-2*n*M*k)^2≤rate*(2*n*M) := by
    nlinarith only [hm,hcross,hsq,sq_nonneg I]
  rw [one_div,mul_comm,←div_eq_mul_inv]
  exact (div_le_iff₀ (by positivity : 0<2*n*M)).mpr hfinal

end RegularPointCoordinates

end OAI
