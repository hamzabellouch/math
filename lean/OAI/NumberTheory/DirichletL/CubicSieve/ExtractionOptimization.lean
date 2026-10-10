import OAI.NumberTheory.DirichletL.CubicSieve.FullNorm

namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma cube_scale_power (M T a : ℝ) (hT : 0 < T) (hTM : T ≤ M) (ha : (1/3 : ℝ) ≤ a) :
    (M/T)^(1/3 : ℝ) * T^a ≤ M^a := by
  have hM : 0 < M := hT.trans_le hTM
  have hbase : 1 ≤ M/T := (one_le_div hT).mpr hTM
  calc
    _ ≤ (M/T)^a * T^a := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hbase ha) (Real.rpow_nonneg hT.le _)
    _ = M^a := by
      rw [Real.div_rpow hM.le hT.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hT a).ne']

lemma extracted_monomial_le (W U T a : ℝ) (hW : 1 ≤ W) (hU : 0 ≤ U)
    (hWT : W^2*U ≤ T) (ha : (1/2 : ℝ) ≤ a) : W*U^a ≤ T^a := by
  have hW0 : 0 ≤ W := by linarith
  have hw : W ≤ (W^2)^a := by
    rw [← Real.rpow_natCast_mul hW0]
    conv_lhs => rw [← Real.rpow_one W]
    exact Real.rpow_le_rpow_of_exponent_le hW (by norm_num; linarith)
  calc
    _ ≤ (W^2)^a * U^a := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hU _)
    _ = (W^2*U)^a := (Real.mul_rpow (sq_nonneg _) hU).symm
    _ ≤ T^a := Real.rpow_le_rpow (mul_nonneg (sq_nonneg _) hU) hWT (by linarith)

lemma extracted_linear_le (W T : ℝ) (hW : 0 ≤ W) (hWT : W^3 ≤ T) :
    W ≤ T^(1/3 : ℝ) := by
  have hh := Real.rpow_le_rpow (pow_nonneg hW 3) hWT (by norm_num : (0 : ℝ) ≤ 1/3)
  rw [← Real.rpow_natCast_mul hW] at hh
  norm_num at hh
  exact hh

lemma extraction_selected_shape (M N W U T ξ : ℝ) (hN : 0 ≤ N)
    (hW : 1 ≤ W) (hU : 0 ≤ U) (hT : 0 < T) (hTM : T ≤ M)
    (hWT : W^2*U ≤ T) (hWcube : W^3 ≤ T) (hξ : 1 ≤ ξ) :
    (M/T)^(1/3 : ℝ) * W * (U^ξ + N + (U*N)^(2/3 : ℝ)) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hM0 : 0 < M := hT.trans_le hTM
  have hH : 0 ≤ (M/T)^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hp : (M/T)^(1/3 : ℝ)*W*U^ξ ≤ M^ξ := by
    calc
      _ = (M/T)^(1/3 : ℝ)*(W*U^ξ) := by ring
      _ ≤ (M/T)^(1/3 : ℝ)*T^ξ := mul_le_mul_of_nonneg_left
        (extracted_monomial_le W U T ξ hW hU hWT (by linarith)) hH
      _ ≤ _ := cube_scale_power M T ξ hT hTM (by linarith)
  have hn : (M/T)^(1/3 : ℝ)*W*N ≤ M^(1/3 : ℝ)*N := by
    apply mul_le_mul_of_nonneg_right _ hN
    calc
      _ ≤ (M/T)^(1/3 : ℝ)*T^(1/3 : ℝ) := mul_le_mul_of_nonneg_left
        (extracted_linear_le W T (by linarith) hWcube) hH
      _ ≤ _ := cube_scale_power M T (1/3) hT hTM le_rfl
  have hc : (M/T)^(1/3 : ℝ)*W*(U*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
    rw [Real.mul_rpow hU hN, Real.mul_rpow (hT.le.trans hTM) hN]
    calc
      _ = ((M/T)^(1/3 : ℝ)*(W*U^(2/3 : ℝ)))*N^(2/3 : ℝ) := by ring
      _ ≤ ((M/T)^(1/3 : ℝ)*T^(2/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (extracted_monomial_le W U T (2/3) hW hU hWT (by norm_num)) hH)
          (Real.rpow_nonneg hN _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (cube_scale_power M T (2/3) hT hTM (by norm_num))
        (Real.rpow_nonneg hN _)
  nlinarith

theorem extraction_min_shape (M N X Y ξ : ℝ) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : 1 ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hT : 0 < X*Y^2 := by positivity
  have hM0 : 0 < M := hT.trans_le hXY
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  by_cases hyx : Y ≤ X
  · apply (mul_le_mul_of_nonneg_left (min_le_left _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N Y X (X*Y^2) ξ hN hY hX0.le hT hXY
      (by nlinarith) (by nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sq_nonneg Y)]) hξ
  · have hxy : X ≤ Y := (lt_of_not_ge hyx).le
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N X Y (X*Y^2) ξ hN hX hY0.le hT hXY
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hX0.le hY0.le)])
      (by nlinarith [sq_le_sq₀ hX0.le hY0.le |>.mpr hxy]) hξ

lemma cubic_cross_shape_absorb (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    (M*N)^(2/3 : ℝ) ≤ M^(1/3 : ℝ)*N + M^ξ := by
  have hM0 : 0 < M := by linarith
  have hfirst : 0 ≤ M^(1/3 : ℝ)*N := mul_nonneg (Real.rpow_nonneg hM0.le _) hN
  have hsecond : 0 ≤ M^ξ := Real.rpow_nonneg hM0.le _
  by_cases hMN : M ≤ N
  · have hN0 : 0 < N := hM0.trans_le hMN
    have hh := Real.rpow_le_rpow hM0.le hMN (by norm_num : (0 : ℝ) ≤ 1/3)
    have hm : M^(2/3 : ℝ) = M^(1/3 : ℝ)*M^(1/3 : ℝ) := by
      rw [← Real.rpow_add hM0]
      congr 1
      ring
    have hn : N^(1/3 : ℝ)*N^(2/3 : ℝ) = N := by
      rw [← Real.rpow_add hN0]
      norm_num
    apply le_trans _ (le_add_of_nonneg_right hsecond)
    rw [Real.mul_rpow hM0.le hN, hm]
    calc
      _ ≤ (M^(1/3 : ℝ)*N^(1/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hM0.le _))
          (Real.rpow_nonneg hN _)
      _ = _ := by rw [mul_assoc, hn]
  · have hNM : N ≤ M := (lt_of_not_ge hMN).le
    apply le_trans _ (le_add_of_nonneg_left hfirst)
    calc
      _ ≤ (M*M)^(2/3 : ℝ) := Real.rpow_le_rpow (mul_nonneg hM0.le hN)
        (mul_le_mul_of_nonneg_left hNM hM0.le) (by norm_num)
      _ = M^(4/3 : ℝ) := by
        rw [Real.mul_rpow hM0.le hM0.le, ← Real.rpow_add hM0]
        congr 1
        ring
      _ ≤ M^ξ := Real.rpow_le_rpow_of_exponent_le hM hξ

theorem extraction_min_two_power (M N X Y ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : (4/3 : ℝ) ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      2*(M^(1/3 : ℝ)*N + M^ξ) := by
  have hh := extraction_min_shape M N X Y ξ hN hX hY hXY (by linarith)
  have hc := cubic_cross_shape_absorb M N ξ hM hN hξ
  linarith

end
end SevenEighths.CubicSieve

end OAI
