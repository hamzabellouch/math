import OAI.NumberTheory.JointDickman.Amplification.GeometricBoxErrors

namespace OAI

/-! # Normalizing the actual frozen-coefficient error before summing boxes -/

namespace JointDickman

theorem coefficient_arc_error_scale {B T X η A C D F G E : ℝ}
    (hB : 1 ≤ B) (hT : 0 < T) (hX : 0 < X) (hη : 0 < η) (hscale : η*T ≤ B)
    (hA : 0 ≤ A) (_hC : 0 ≤ C) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hE : E ≤ X*(A*B^(-50 : ℝ)+C/B)*(D*B^(-(3/2 : ℝ))/(T*X))+
      B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G)) :
    T*B*E ≤ (D*(A+C)+2*F^2*G/η)*B^(-(3/2 : ℝ)) := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBne := hBpos.ne'
  have hTB : T ≤ B/η := (le_div_iff₀ hη).mpr (by nlinarith [hscale])
  have hp50 : B*B^(-50 : ℝ) ≤ 1 := by
    have he : B*B^(-50 : ℝ) = B^(-49 : ℝ) := by
      calc
        _ = B^(1 : ℝ)*B^(-50 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hBpos]; norm_num
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos hB (by norm_num)
  have hmain : T*B*(X*(A*B^(-50 : ℝ)+C/B)*(D*B^(-(3/2 : ℝ))/(T*X))) ≤
      D*(A+C)*B^(-(3/2 : ℝ)) := by
    calc
      _ = D*(A*(B*B^(-50 : ℝ))+C)*B^(-(3/2 : ℝ)) := by field_simp
      _ ≤ _ := by
        gcongr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp50 hA
  have hnum : B^12*(B^12+1) ≤ 2*B^24 := by
    have hone : 1 ≤ B^12 := one_le_pow₀ hB
    have hp : B^12*B^12 = B^24 := by ring
    nlinarith
  have hden : ((B^13)^10)⁻¹ ≤ (B^28)⁻¹ := by
    apply inv_anti₀ (by positivity)
    rw [← pow_mul]
    exact pow_le_pow_right₀ hB (by norm_num : 28 ≤ 13*10)
  have hfrac : (F/B)^2 ≤ F^2 := pow_le_pow_left₀ (by positivity) (div_le_self hF hB) 2
  have htail : B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G) ≤ 2*F^2*G/B^4 := by
    calc
      _ ≤ (2*B^24)*(F^2*(B^28)⁻¹*G) := by gcongr
      _ = _ := by field_simp
  have hp2 : B^(-2 : ℝ) ≤ B^(-(3/2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
  have htail' : T*B*(B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G)) ≤
      (2*F^2*G/η)*B^(-(3/2 : ℝ)) := by
    calc
      _ ≤ (B/η)*B*(2*F^2*G/B^4) := by gcongr
      _ = (2*F^2*G/η)*B^(-2 : ℝ) := by
        rw [Real.rpow_neg hBpos.le,Real.rpow_ofNat]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hp2 (by positivity)
  calc
    _ ≤ T*B*(X*(A*B^(-50 : ℝ)+C/B)*(D*B^(-(3/2 : ℝ))/(T*X))+
        B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = T*B*(X*(A*B^(-50 : ℝ)+C/B)*(D*B^(-(3/2 : ℝ))/(T*X)))+
        T*B*(B^12*(B^12+1)*((F/B)^2*((B^13)^10)⁻¹*G)) := mul_add _ _ _
    _ ≤ D*(A+C)*B^(-(3/2 : ℝ))+(2*F^2*G/η)*B^(-(3/2 : ℝ)) := add_le_add hmain htail'
    _ = _ := by ring

end JointDickman

end OAI
