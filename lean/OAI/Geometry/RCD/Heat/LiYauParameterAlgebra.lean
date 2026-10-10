import OAI.Geometry.RCD.Heat.LiYauRiccatiAlgebra

namespace OAI

/-! # The scalar Li--Yau reduction for every parameter greater than one

Allowing the parameter to approach one is needed to eliminate the
osmotic energy; the fixed parameter-two estimate is insufficient.
-/

namespace RegularPointCoordinates

theorem liYau_parameter_algebra {n M k I D rate α : ℝ}
    (hn : 0 < n) (hM : 0 < M) (hk : 0 ≤ k) (hI : 0 ≤ I) (hα : 1 < α)
    (hbound : (2/n)*(D-I)^2-2*k*M*I ≤ M*rate)
    (hthreshold : n*M*α^2*k/(2*(α-1)) ≤ I-α*D) :
    (2/(n*M*α^2))*(I-α*D-n*M*α^2*k/(2*(α-1)))^2 ≤ rate := by
  let Y := I-α*D
  let B := n*M*α^2*k/(2*(α-1))
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hden : 0 < 2*(α-1) := by linarith
  have hB : 0 ≤ B := div_nonneg (by positivity) hden.le
  have hY : 0 ≤ Y := hB.trans hthreshold
  have hcross : 0 ≤ I*(2*(α-1)*Y-n*M*α^2*k) := by
    apply mul_nonneg hI
    have hh := (div_le_iff₀ hden).mp hthreshold
    dsimp only [Y]
    nlinarith only [hh]
  have hb := mul_le_mul_of_nonneg_left hbound (show 0 ≤ n*α^2 by positivity)
  have he : (n*α^2)*((2/n)*(D-I)^2-2*k*M*I) =
      2*(Y+(α-1)*I)^2-2*n*α^2*k*M*I := by
    dsimp only [Y]
    field_simp
    ring
  rw [he] at hb
  have hrest : 0 ≤ 2*((α-1)*I)^2+2*(I*(2*(α-1)*Y-n*M*α^2*k)) :=
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (by norm_num) hcross)
  have he' : 2*(Y+(α-1)*I)^2-2*n*α^2*k*M*I =
      2*Y^2+(2*((α-1)*I)^2+2*(I*(2*(α-1)*Y-n*M*α^2*k))) := by ring
  rw [he'] at hb
  have hs : (Y-B)^2 ≤ Y^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hthreshold) (sub_le_self Y hB) 2
  have hfinal : 2*(Y-B)^2 ≤ rate*(n*M*α^2) := by
    nlinarith only [hs,hb,hrest]
  rw [div_mul_eq_mul_div,div_le_iff₀ (show 0 < n*M*α^2 by positivity)]
  exact hfinal

end RegularPointCoordinates

end OAI
