import Mathlib

namespace OAI

noncomputable section

open Real

namespace Problem367

theorem log_sq_le_four_mul {I : ℝ} (hI : 1 ≤ I) :
    (Real.log I) ^ 2 ≤ 4 * I := by
  have hI0 : 0 ≤ I := le_trans zero_le_one hI
  have hlog0 : 0 ≤ Real.log I := Real.log_nonneg hI
  have hsqrt : 0 < Real.sqrt I := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hI)
  have hlog := Real.log_le_sub_one_of_pos hsqrt
  rw [Real.log_sqrt hI0] at hlog
  have hle : Real.log I ≤ 2 * Real.sqrt I := by linarith
  nlinarith [Real.sq_sqrt hI0, sq_nonneg (2 * Real.sqrt I - Real.log I)]

theorem log_three_halves_le_four_mul {I : ℝ} (hI : 1 ≤ I) :
    (Real.log I) ^ ((3 : ℝ) / 2) ≤ 4 * I := by
  have hlog0 : 0 ≤ Real.log I := Real.log_nonneg hI
  by_cases hlog1 : Real.log I ≤ 1
  · have hpow : (Real.log I) ^ ((3 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one hlog0 hlog1 (by norm_num)
    linarith
  · have hpow := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hlog1)
      (show (3 : ℝ) / 2 ≤ 2 by norm_num)
    exact hpow.trans (by simpa using log_sq_le_four_mul hI)

theorem sqrt_mul_sqrt_le_of_le_mul {S V C : ℝ}
    (_hS : 0 ≤ S) (hV : 0 ≤ V) (hC : 1 ≤ C) (hSV : S ≤ C * V) :
    Real.sqrt V * Real.sqrt S ≤ C * V := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  calc
    Real.sqrt V * Real.sqrt S = Real.sqrt (V * S) := (Real.sqrt_mul hV S).symm
    _ ≤ Real.sqrt (V * (C * V)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hSV hV)
    _ = Real.sqrt C * V := by
      rw [Real.sqrt_mul hV, Real.sqrt_mul hC0]
      calc
        Real.sqrt V * (Real.sqrt C * Real.sqrt V) = Real.sqrt C * (Real.sqrt V)^2 := by ring
        _ = Real.sqrt C * V := by rw [Real.sq_sqrt hV]
    _ ≤ C * V := by
      gcongr
      exact Real.sqrt_le_self_iff.2 (Or.inr hC)

theorem endpoint_sums_critical_reduction
    {D Q L Z S V C H I R W : ℝ}
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hI : 1 ≤ I)
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hVH : V ≤ H)
    (hSV : S ≤ C * V) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hQ : Q ≤ C * (S * (R + (Real.log I)^2) + V^2))
    (hL : L ≤ C * (V * (W + Real.log I) + V^2))
    (hZ : Z ≤ C * (Real.sqrt S * (W + (Real.log I)^((3 : ℝ)/2)) + V))
    (hD : D ≤ C * (V + Q + L + Real.sqrt V * Z)) :
    D ≤ C^2 * (9*C + 3*H + 3) * (S*R + V*(I+W)) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hI0 : 0 ≤ I := le_trans zero_le_one hI
  have hlog0 : 0 ≤ Real.log I := Real.log_nonneg hI
  have hlog : Real.log I ≤ I := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlog2 := log_sq_le_four_mul hI
  have hlog3 := log_three_halves_le_four_mul hI
  have hsqrt := sqrt_mul_sqrt_le_of_le_mul hS hV hC hSV
  have hsqrtV : Real.sqrt V ≤ H :=
    (Real.sqrt_le_sqrt hVH).trans (Real.sqrt_le_self_iff.2 (Or.inr hH))
  have hV2 : V^2 ≤ H*V := by nlinarith
  have hVI : V ≤ V*I := by nlinarith
  have hHV : H*V ≤ H*V*I := by nlinarith
  have hSlog : S * (Real.log I)^2 ≤ 4*C*V*I := by
    calc
      S * (Real.log I)^2 ≤ (C*V) * (4*I) := mul_le_mul hSV hlog2 (sq_nonneg _) (by positivity)
      _ = 4*C*V*I := by ring
  have hQ' : Q ≤ C*(S*R + (4*C+H)*V*I) := by
    have hstep : S*(R+(Real.log I)^2)+V^2 ≤ S*R+(4*C+H)*V*I := by
      nlinarith
    exact hQ.trans (mul_le_mul_of_nonneg_left hstep hC0)
  have hL' : L ≤ C*(V*W + (1+H)*V*I) := by
    have hstep : V*(W+Real.log I)+V^2 ≤ V*W+(1+H)*V*I := by
      have := mul_le_mul_of_nonneg_left hlog hV
      nlinarith
    exact hL.trans (mul_le_mul_of_nonneg_left hstep hC0)
  have hZ' : Real.sqrt V * Z ≤ C*(C*V*W+(4*C+H)*V*I) := by
    calc
      Real.sqrt V * Z ≤ Real.sqrt V * (C*(Real.sqrt S*(W+(Real.log I)^((3:ℝ)/2))+V)) :=
        mul_le_mul_of_nonneg_left hZ (Real.sqrt_nonneg _)
      _ = C*((Real.sqrt V*Real.sqrt S)*(W+(Real.log I)^((3:ℝ)/2)) + Real.sqrt V*V) := by ring
      _ ≤ C*((C*V)*(W+4*I)+H*V*I) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        apply add_le_add
        · exact mul_le_mul hsqrt (add_le_add le_rfl hlog3)
            (add_nonneg hW (Real.rpow_nonneg hlog0 _)) (by positivity)
        · exact (mul_le_mul_of_nonneg_right hsqrtV hV).trans hHV
      _ = C*(C*V*W+(4*C+H)*V*I) := by ring
  have hstart : D ≤ C*(V+C*(S*R+(4*C+H)*V*I)+C*(V*W+(1+H)*V*I)+
      C*(C*V*W+(4*C+H)*V*I)) := by
    apply hD.trans
    gcongr
  have hscale : 0 ≤ S*R := mul_nonneg hS hR
  have hVI0 : 0 ≤ V*I := mul_nonneg hV hI0
  have hVW0 : 0 ≤ V*W := mul_nonneg hV hW
  have hC2 : C ≤ C^2 := by nlinarith
  have hCpos : 0 ≤ C^2 := sq_nonneg C
  have hCV : C*V ≤ C^2*(V*I) := mul_le_mul hC2 hVI hV hCpos
  have hcoef1 : 1 ≤ 9*C+3*H+3 := by linarith
  have hcoef2 : 8*C+3*H+2 ≤ 9*C+3*H+3 := by linarith
  have hcoef3 : C+1 ≤ 9*C+3*H+3 := by linarith
  calc
    D ≤ C*V + C^2*(S*R) + C^2*(8*C+3*H+1)*(V*I) +
        C^2*(C+1)*(V*W) := by convert hstart using 1; ring
    _ ≤ C^2*(V*I) + C^2*(S*R) + C^2*(8*C+3*H+1)*(V*I) +
        C^2*(C+1)*(V*W) := by gcongr
    _ = C^2*(S*R+(8*C+3*H+2)*(V*I)+(C+1)*(V*W)) := by ring
    _ ≤ C^2*((9*C+3*H+3)*(S*R)+(9*C+3*H+3)*(V*I)+
        (9*C+3*H+3)*(V*W)) := by
      apply mul_le_mul_of_nonneg_left _ hCpos
      apply add_le_add
      · apply add_le_add
        · simpa using mul_le_mul_of_nonneg_right hcoef1 hscale
        · exact mul_le_mul_of_nonneg_right hcoef2 hVI0
      · exact mul_le_mul_of_nonneg_right hcoef3 hVW0
    _ = C^2*(9*C+3*H+3)*(S*R+V*(I+W)) := by ring

theorem small_time_scale_reduction {S B V I J t : ℝ}
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hI : 1 ≤ I) (hJ : 0 < J) (ht : 0 < t)
    (hS : S ≤ B*V*(t^((1:ℝ)/4)+I/J)) :
    S/t + V*(I+t^(-(3:ℝ)/4)) ≤
      (B+1)*V*I*(1+t^(-(3:ℝ)/4)+1/(t*J)) := by
  have hI0 : 0 ≤ I := le_trans zero_le_one hI
  have hW : 0 ≤ t^(-(3:ℝ)/4) := Real.rpow_nonneg ht.le _
  have htJ : 0 < t*J := mul_pos ht hJ
  have hpow : t^((1:ℝ)/4)/t = t^(-(3:ℝ)/4) := by
    rw [show -(3:ℝ)/4 = (1:ℝ)/4-1 by norm_num, Real.rpow_sub ht, Real.rpow_one]
  have hnoise : S/t ≤ B*V*(t^(-(3:ℝ)/4)+I/(t*J)) := by
    calc
      S/t ≤ (B*V*(t^((1:ℝ)/4)+I/J))/t := div_le_div_of_nonneg_right hS ht.le
      _ = B*V*(t^((1:ℝ)/4)/t+I/(t*J)) := by field_simp
      _ = B*V*(t^(-(3:ℝ)/4)+I/(t*J)) := by rw [hpow]
  have hfirst : (B+1)*V*t^(-(3:ℝ)/4) ≤ (B+1)*V*I*t^(-(3:ℝ)/4) := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hI (show 0 ≤ (B+1)*V by positivity)) hW
    simpa using this
  have hsecond : B*V*I/(t*J) ≤ (B+1)*V*I/(t*J) := by gcongr; linarith
  have hthird : V*I ≤ (B+1)*V*I := by nlinarith [mul_nonneg hB (mul_nonneg hV hI0)]
  calc
    S/t + V*(I+t^(-(3:ℝ)/4)) ≤ B*V*(t^(-(3:ℝ)/4)+I/(t*J)) + V*(I+t^(-(3:ℝ)/4)) :=
      add_le_add hnoise le_rfl
    _ = (B+1)*V*t^(-(3:ℝ)/4) + B*V*I/(t*J) + V*I := by ring
    _ ≤ (B+1)*V*I*t^(-(3:ℝ)/4) + (B+1)*V*I/(t*J) + (B+1)*V*I :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = (B+1)*V*I*(1+t^(-(3:ℝ)/4)+1/(t*J)) := by ring

theorem critical_differential_bound_of_endpoint_sums
    {D Q L Z S V C H I B J t : ℝ}
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hI : 1 ≤ I) (hB : 0 ≤ B)
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hVH : V ≤ H) (hSV : S ≤ C*V)
    (hJ : 0 < J) (ht : 0 < t)
    (hsmall : S ≤ B*V*(t^((1:ℝ)/4)+I/J))
    (hQ : Q ≤ C*(S*(1/t+(Real.log I)^2)+V^2))
    (hL : L ≤ C*(V*(t^(-(3:ℝ)/4)+Real.log I)+V^2))
    (hZ : Z ≤ C*(Real.sqrt S*(t^(-(3:ℝ)/4)+(Real.log I)^((3:ℝ)/2))+V))
    (hD : D ≤ C*(V+Q+L+Real.sqrt V*Z)) :
    D ≤ (C^2*(9*C+3*H+3)*(B+1))*V*I*
      (1+t^(-(3:ℝ)/4)+1/(t*J)) := by
  have hscale := endpoint_sums_critical_reduction hC hH hI hS hV hVH hSV
    (show 0 ≤ 1/t by positivity) (Real.rpow_nonneg ht.le _) hQ hL hZ hD
  have hreduce := small_time_scale_reduction hB hV hI hJ ht hsmall
  have hconst : 0 ≤ C^2*(9*C+3*H+3) := by positivity
  calc
    D ≤ C^2*(9*C+3*H+3)*(S/t+V*(I+t^(-(3:ℝ)/4))) := by
      simpa only [mul_one_div] using hscale
    _ ≤ C^2*(9*C+3*H+3)*((B+1)*V*I*(1+t^(-(3:ℝ)/4)+1/(t*J))) :=
      mul_le_mul_of_nonneg_left hreduce hconst
    _ = (C^2*(9*C+3*H+3)*(B+1))*V*I*(1+t^(-(3:ℝ)/4)+1/(t*J)) := by ring

end Problem367

end

end OAI
