import OAI.Geometry.RCD.Heat.ScaledTimeError

namespace OAI

/-! # Uniform errors when fixing the reference heat time at ε -/

namespace RegularPointCoordinates

theorem scaled_reference_upper_error {n k ε δ s : ℝ}
    (hn : 0≤n) (hk : 0≤k) (hε : 0<ε) (hε1 : ε≤1)
    (hδ : 0<δ) (hδs : δ≤ s) :
    ε*n*(Real.log ε-Real.log (ε*s/2)+k*(ε-ε*s/2))≤n*(2/δ+k) := by
  have hs : 0<s := hδ.trans_le hδs
  have ha : 0<ε*s/2 := by positivity
  have hratio : Real.log ε-Real.log (ε*s/2)=Real.log (2/s) := by
    rw [←Real.log_div hε.ne' ha.ne']
    congr 1
    field_simp
  rw [hratio]
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0<(2:ℝ)/s)
  have hdiv : (2:ℝ)/s≤2/δ := div_le_div_of_nonneg_left (by norm_num) hδ hδs
  have hgap : ε-ε*s/2≤1 := by nlinarith only [hε1,mul_nonneg hε.le hs.le]
  have hkb := mul_le_mul_of_nonneg_left hgap hk
  have hb : Real.log (2/s)+k*(ε-ε*s/2)≤2/δ+k := by linarith only [hlog,hdiv,hkb]
  calc
    _ ≤ ε*n*(2/δ+k) := mul_le_mul_of_nonneg_left hb (mul_nonneg hε.le hn)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left hn hε1) (by positivity)

theorem scaled_reference_lower_error {C D R ε δ s : ℝ}
    (hC : 0≤C) (hD : 0≤D) (hε : 0<ε) (hε1 : ε≤1)
    (hδ : 0<δ) (hδs : δ≤ s) :
    ε*(C+D*R^2/(ε*s/2))≤C+2*D*R^2/δ := by
  have hs : 0<s := hδ.trans_le hδs
  have he : ε*(C+D*R^2/(ε*s/2))=ε*C+2*D*R^2/s := by
    field_simp
  rw [he]
  exact add_le_add (mul_le_of_le_one_left hC hε1)
    (div_le_div_of_nonneg_left (by positivity) hδ hδs)

end RegularPointCoordinates

end OAI
