import OAI.Geometry.RCD.Heat.OsmoticEnergyAlgebra

namespace OAI

/-! # A noise-dependent Li--Yau parameter gives an explicit osmotic rate -/

namespace RegularPointCoordinates

theorem osmotic_noise_rate {c S E R J B D W : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hB : 0 ≤ B) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hV : c^2*(S-2*E) ≤ B) (hR : c^2*R ≤ c*D) (hJ : |c*J| ≤ W)
    (h : S+2*E ≤ (c/(2+c))*(S-2*E)+(2/(2+c))*(R-(1+c)*J)) :
    c^2*(S+2*E) ≤ c*(B+D+2*W) := by
  have hd : 0 < 2+c := by linarith
  have hq0 : 0 ≤ c/(2+c) := div_nonneg hc.le hd.le
  have hq : c/(2+c) ≤ c := (div_le_iff₀ hd).mpr (by nlinarith)
  have hr0 : 0 ≤ 2/(2+c) := div_nonneg (by norm_num) hd.le
  have hr : 2/(2+c) ≤ 1 := (div_le_iff₀ hd).mpr (by linarith)
  have hj : -(c^2*J) ≤ c*W := by
    have hj := (abs_le.mp hJ).1
    nlinarith
  have hα : 0 ≤ 1+c := by linarith
  have hα1 : 1+c ≤ 2 := by linarith
  calc
    c^2*(S+2*E) ≤ c^2*((c/(2+c))*(S-2*E)+(2/(2+c))*(R-(1+c)*J)) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg c)
    _ = (c/(2+c))*(c^2*(S-2*E))+
        (2/(2+c))*(c^2*R+(1+c)*(-(c^2*J))) := by ring
    _ ≤ (c/(2+c))*B+(2/(2+c))*(c*D+(1+c)*(c*W)) :=
      add_le_add (mul_le_mul_of_nonneg_left hV hq0)
        (mul_le_mul_of_nonneg_left (add_le_add hR
          (mul_le_mul_of_nonneg_left hj hα)) hr0)
    _ ≤ c*B+(c*D+2*(c*W)) := by
      apply add_le_add (mul_le_mul_of_nonneg_right hq hB)
      calc
        (2/(2+c))*(c*D+(1+c)*(c*W)) ≤ c*D+(1+c)*(c*W) :=
          mul_le_of_le_one_left (by positivity) hr
        _ ≤ c*D+2*(c*W) := add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hα1 (mul_nonneg hc.le hW))
    _ = c*(B+D+2*W) := by ring

end RegularPointCoordinates

end OAI
