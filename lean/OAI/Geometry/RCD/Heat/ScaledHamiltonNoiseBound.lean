import OAI.Geometry.RCD.Heat.FisherScalarComparison

namespace OAI

/-! # The vanishing noise term in the scaled Hamilton estimate -/

namespace RegularPointCoordinates

theorem scaled_hamilton_noise_bound {k C D ε s δ R G t : ℝ}
    (hk : 0≤k) (hC : 0≤C) (hD : 0≤D) (hε : 0<ε) (hε1 : ε≤1)
    (hδ : 0<δ) (hδs : δ≤ s) (hs1 : s≤1) (ht : t=ε*s/4)
    (hG : t*Real.exp (-2*k*t)*G^2≤C+D*R^2/t) :
    (ε*G)^2≤Real.exp k*(4*C*ε/δ+16*D*R^2/δ^2) := by
  have hs : 0<s := hδ.trans_le hδs
  have ht0 : 0<t := by rw [ht]; positivity
  have hratio : ε/t=4/s := by rw [ht]; field_simp
  have hb0 : 0≤ε/t := div_nonneg hε.le ht0.le
  have hb : ε/t≤4/δ := by
    rw [hratio]
    exact div_le_div_of_nonneg_left (by norm_num) hδ hδs
  have ha : ε^2/t≤4*ε/δ := by
    calc
      _ = ε*(ε/t) := by ring
      _ ≤ ε*(4/δ) := mul_le_mul_of_nonneg_left hb hε.le
      _ = _ := by ring
  have hb2 : (ε/t)^2≤16/δ^2 := by
    simpa only [div_pow,show (4:ℝ)^2=16 by norm_num] using pow_le_pow_left₀ hb0 hb 2
  have ht2 : 2*t≤1 := by
    have hm := mul_le_mul hε1 hs1 hs.le (by norm_num : (0:ℝ)≤1)
    rw [ht]
    nlinarith only [hm]
  have he : Real.exp (2*k*t)≤Real.exp k :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left ht2 hk])
  have hinv : Real.exp (2*k*t)*Real.exp (-2*k*t)=1 := by
    rw [←Real.exp_add]
    have hz : 2*k*t+(-2*k*t)=0 := by ring
    rw [hz,Real.exp_zero]
  have hbase : (ε*G)^2≤Real.exp (2*k*t)*(C*(ε^2/t)+D*R^2*(ε/t)^2) := by
    have hm := mul_le_mul_of_nonneg_left hG
      (show 0≤ε^2/t*Real.exp (2*k*t) by positivity)
    calc
      _ = ε^2*(Real.exp (2*k*t)*Real.exp (-2*k*t))*G^2 := by rw [hinv]; ring
      _ = (ε^2/t*Real.exp (2*k*t))*(t*Real.exp (-2*k*t)*G^2) := by field_simp
      _ ≤ (ε^2/t*Real.exp (2*k*t))*(C+D*R^2/t) := hm
      _ = _ := by field_simp
  have hi : C*(ε^2/t)+D*R^2*(ε/t)^2≤4*C*ε/δ+16*D*R^2/δ^2 := by
    have hc := mul_le_mul_of_nonneg_left ha hC
    have hd := mul_le_mul_of_nonneg_left hb2 (mul_nonneg hD (sq_nonneg R))
    calc
      _ ≤ C*(4*ε/δ)+D*R^2*(16/δ^2) := add_le_add hc hd
      _ = _ := by ring
  exact hbase.trans (mul_le_mul he hi (by positivity) (Real.exp_pos _).le)

end RegularPointCoordinates

end OAI
