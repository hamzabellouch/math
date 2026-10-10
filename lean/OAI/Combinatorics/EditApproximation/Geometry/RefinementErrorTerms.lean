import OAI.Combinatorics.EditApproximation.Refinement.ComputedStageTime

namespace OAI

/-! Explicit estimates for the actual four parts of the refinement error. -/

namespace EditApproximation

theorem refinement_grid_error {ell H M J P : ℝ}
    (hell : 1 ≤ ell) (hH : ell ≤ H) (hM : M ≤ H)
    (hJ : 0 ≤ J) (hdepth : J * ell ≤ 100 * H) (hP : H ^ 20 ≤ P) :
    (8 * M + 512 * ell) * J / P ≤ 52000 / H ^ 18 := by
  have hHone : 1 ≤ H := hell.trans hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hHone
  have hJbound : J ≤ 100 * H := by
    have hm := mul_le_mul_of_nonneg_left hell hJ
    nlinarith only [hm, hdepth]
  have hcoef : 8 * M + 512 * ell ≤ 520 * H := by linarith only [hM, hH]
  have hnum := mul_le_mul hcoef hJbound hJ (by positivity : (0 : ℝ) ≤ 520 * H)
  have hPpos : 0 < P := (pow_pos hHpos 20).trans_le hP
  calc
    _ ≤ 52000 * H ^ 2 / P := div_le_div_of_nonneg_right (by nlinarith only [hnum]) hPpos.le
    _ ≤ 52000 * H ^ 2 / H ^ 20 := div_le_div_of_nonneg_left (by positivity) (pow_pos hHpos 20) hP
    _ = _ := by field_simp

theorem refinement_excluded_error {ell root H J P T S : ℝ}
    (hell : 1 ≤ ell) (hroot : 1 ≤ root) (hrootPower : root ^ 4 = H)
    (hS : 0 < S) (hcount : S * ell ^ 2 = H)
    (hJP : J / P ≤ 1) (hJT : J / T ≤ 100 * root / ell) :
    40000 * ell ^ 2 * root * (1 + J / P + J / T) / S ≤
      8040000 * ell ^ 4 / root ^ 2 := by
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hrootpos : 0 < root := lt_of_lt_of_le zero_lt_one hroot
  have hSrepr : S = root ^ 4 / ell ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hellpos.ne')).2
    exact hcount.trans hrootPower.symm
  have hbracket : 1 + J / P + J / T ≤ 2 + 100 * root / ell := by linarith only [hJP, hJT]
  have hfirst : 80000 * ell ^ 4 / root ^ 3 ≤ 80000 * ell ^ 4 / root ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos hrootpos 2)
    have hm := mul_le_mul_of_nonneg_right hroot (pow_nonneg hrootpos.le 2)
    nlinarith only [hm, show root * root ^ 2 = root ^ 3 by ring]
  have hellPower : ell ^ 3 ≤ ell ^ 4 := pow_le_pow_right₀ hell (by decide : 3 ≤ 4)
  have hsecond : 4000000 * ell ^ 3 / root ^ 2 ≤ 4000000 * ell ^ 4 / root ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hellPower (by norm_num)) (pow_nonneg hrootpos.le 2)
  calc
    _ ≤ 40000 * ell ^ 2 * root * (2 + 100 * root / ell) / S :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbracket (by positivity)) hS.le
    _ = 80000 * ell ^ 4 / root ^ 3 + 4000000 * ell ^ 3 / root ^ 2 := by
      rw [hSrepr]
      field_simp
      ring
    _ ≤ 80000 * ell ^ 4 / root ^ 2 + 4000000 * ell ^ 4 / root ^ 2 := add_le_add hfirst hsecond
    _ = 4080000 * ell ^ 4 / root ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by norm_num : (4080000 : ℝ) ≤ 8040000) (pow_nonneg hellpos.le 4)) (pow_nonneg hrootpos.le 2)

theorem refinement_depth_ratios {ell H root J P T S : ℝ}
    (hell : 1 ≤ ell) (hH : 100 ≤ H) (hroot : 0 < root) (hrootPower : root ^ 4 = H)
    (hJ : 0 ≤ J) (hdepth : J * ell ≤ 100 * H)
    (hP : H ^ 20 ≤ P) (hT : root ^ 3 ≤ T)
    (hS : 0 < S) (hcount : S * ell ^ 2 = H) :
    J / P ≤ 1 ∧ J / T ≤ 100 * root / ell ∧ J / S ≤ 100 * ell := by
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hHone : 1 ≤ H := by linarith only [hH]
  have hHpos : 0 < H := by linarith only [hH]
  have hJbound : J ≤ 100 * H := by
    have hm := mul_le_mul_of_nonneg_left hell hJ
    nlinarith only [hm, hdepth]
  have hPbound : 100 * H ≤ P := by
    calc
      100 * H ≤ H ^ 2 := by nlinarith only [hH, sq_nonneg H]
      _ ≤ H ^ 20 := pow_le_pow_right₀ hHone (by decide : 2 ≤ 20)
      _ ≤ P := hP
  have hPpos : 0 < P := (pow_pos hHpos 20).trans_le hP
  have hTpos : 0 < T := (pow_pos hroot 3).trans_le hT
  refine ⟨(div_le_one₀ hPpos).2 (hJbound.trans hPbound), ?_, ?_⟩
  · apply (div_le_div_iff₀ hTpos hellpos).2
    have hm := mul_le_mul_of_nonneg_left hT (show 0 ≤ 100 * root by positivity)
    have hid : (100 * root) * root ^ 3 = 100 * H := by rw [← hrootPower]; ring
    rw [hid] at hm
    exact hdepth.trans hm
  · apply (div_le_iff₀ hS).2
    apply le_of_mul_le_mul_right _ hellpos
    calc
      J * ell ≤ 100 * H := hdepth
      _ = (100 * ell * S) * ell := by rw [← hcount]; ring

theorem refinement_ordinary_error {ell root q J S : ℝ}
    (hell : 1 ≤ ell) (hroot : 0 < root) (hq : 1 ≤ q)
    (hJS : J / S ≤ 100 * ell) :
    2 * J / S * (1 / root + 4 * (1 / ell ^ 4) * ell +
        64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4)) + 2 * (1 / ell ^ 10)) ≤
      200 * ell / root + 1000000 * q / ell ^ 2 := by
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let bracket := 1 / root + 4 * (1 / ell ^ 4) * ell +
    64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4)) + 2 * (1 / ell ^ 10)
  have hbracket : 0 ≤ bracket := by dsimp only [bracket]; positivity
  have htwo : 2 * J / S ≤ 200 * ell := by
    calc
      2 * J / S = 2 * (J / S) := by ring
      _ ≤ 2 * (100 * ell) := mul_le_mul_of_nonneg_left hJS (by norm_num)
      _ = _ := by ring
  have hpower : ell ^ 2 ≤ ell ^ 9 := pow_le_pow_right₀ hell (by decide : 2 ≤ 9)
  have hsmall : 400 / ell ^ 9 ≤ 400 / ell ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hellpos 2) hpower
  have hcoeff : 26400 + 51200 * q + 400 ≤ 1000000 * q := by linarith only [hq]
  calc
    _ ≤ 200 * ell * bracket := mul_le_mul_of_nonneg_right htwo hbracket
    _ = 200 * ell / root + (26400 + 51200 * q) / ell ^ 2 + 400 / ell ^ 9 := by
      dsimp only [bracket]
      field_simp
      ring
    _ ≤ 200 * ell / root + (26400 + 51200 * q + 400) / ell ^ 2 := by
      have h := add_le_add_right hsmall (200 * ell / root + (26400 + 51200 * q) / ell ^ 2)
      simpa only [add_div, add_assoc] using h
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_right hcoeff (pow_nonneg hellpos.le 2)) _

theorem refinement_numerical_error {ell H J S : ℝ}
    (hell : 0 ≤ ell) (hH : 1 ≤ H) (hJ : 0 ≤ J) (hS : 0 < S)
    (hdepth : J * ell ≤ 100 * H) :
    2 * J / S * (64 * ell * (S / H ^ 3) + 2 * S * (1 / H ^ 4) * ell) ≤ 13200 / H ^ 2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hsmall : 4 * ell * J / H ^ 4 ≤ 4 * ell * J / H ^ 3 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hHpos 3)
      (pow_le_pow_right₀ hH (by decide : 3 ≤ 4))
  calc
    _ = 128 * ell * J / H ^ 3 + 4 * ell * J / H ^ 4 := by field_simp; ring
    _ ≤ 128 * ell * J / H ^ 3 + 4 * ell * J / H ^ 3 := add_le_add_right hsmall _
    _ = 132 * (J * ell) / H ^ 3 := by ring
    _ ≤ 132 * (100 * H) / H ^ 3 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdepth (by norm_num)) (pow_nonneg hHpos.le 3)
    _ = _ := by field_simp; ring

theorem refinement_error_from_stage_bounds {ell H root q M J P T S : ℝ}
    (hell : 64000000000000 ≤ ell) (hH : ell ^ 2 ≤ H)
    (hroot : ell ^ 4 ≤ root) (hrootPower : root ^ 4 = H)
    (hq : 1 ≤ q) (hqSquare : q ^ 2 ≤ ell)
    (hM : M ≤ H) (hJ : 0 ≤ J) (hdepth : J * ell ≤ 100 * H)
    (hP : H ^ 20 ≤ P) (hT : root ^ 3 ≤ T)
    (hS : 0 < S) (hcount : S * ell ^ 2 = H) :
    (8 * M + 512 * ell) * J / P +
      (40000 * root * ell ^ 2 * (1 + J / P + J / T) +
        2 * J * (1 / root + 4 * (1 / ell ^ 4) * ell +
          (64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4) + S / H ^ 3) +
            2 * (1 / ell ^ 10) + 2 * S * (1 / H ^ 4) * ell))) / S < 1 / ell := by
  have hellone : 1 ≤ ell := by linarith only [hell]
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hellone
  have hHell : ell ≤ H := (by nlinarith only [hellone] : ell ≤ ell ^ 2).trans hH
  have hHlarge : 100 ≤ H := by linarith only [hell, hHell]
  have hrootone : 1 ≤ root := (one_le_pow₀ hellone).trans hroot
  have hrootpos : 0 < root := lt_of_lt_of_le zero_lt_one hrootone
  have hratios := refinement_depth_ratios hellone hHlarge hrootpos hrootPower hJ hdepth hP hT hS hcount
  have hgrid := refinement_grid_error hellone hHell hM hJ hdepth hP
  have hbad := refinement_excluded_error hellone hrootone hrootPower hS hcount hratios.1 hratios.2.1
  have hordinary := refinement_ordinary_error hellone hrootpos hq hratios.2.2
  have hnumeric := refinement_numerical_error (zero_le_one.trans hellone) (by linarith only [hHlarge]) hJ hS hdepth
  have hsplit : (8 * M + 512 * ell) * J / P +
      (40000 * root * ell ^ 2 * (1 + J / P + J / T) +
        2 * J * (1 / root + 4 * (1 / ell ^ 4) * ell +
          (64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4) + S / H ^ 3) +
            2 * (1 / ell ^ 10) + 2 * S * (1 / H ^ 4) * ell))) / S =
      (8 * M + 512 * ell) * J / P +
        40000 * ell ^ 2 * root * (1 + J / P + J / T) / S +
        2 * J / S * (1 / root + 4 * (1 / ell ^ 4) * ell +
          64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4)) + 2 * (1 / ell ^ 10)) +
        2 * J / S * (64 * ell * (S / H ^ 3) + 2 * S * (1 / H ^ 4) * ell) := by ring
  rw [hsplit]
  apply lt_of_le_of_lt _ (refinement_error_envelope hell hH hroot (zero_le_one.trans hq) hqSquare)
  linarith only [hgrid, hbad, hordinary, hnumeric]

noncomputable def computedRefinementError (N nx : ℕ) : ℝ :=
  let ell : ℝ := inputSmallLog N
  let H : ℝ := inputHeight N
  let M : ℝ := (integerParameters N).M
  let J : ℝ := intervalTreeDepth (integerParameters N).M nx
  let P : ℝ := (integerParameters N).P
  let T : ℝ := (integerParameters N).T
  let S : ℝ := (integerParameters N).S
  let root := heightQuarterRoot N
  let q : ℝ := coarseExponent (inputSmallLog N) + 21
  (8 * M + 512 * ell) * J / P +
    (40000 * root * ell ^ 2 * (1 + J / P + J / T) +
      2 * J * (1 / root + 4 * (1 / ell ^ 4) * ell +
        (64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4) + S / H ^ 3) +
          2 * (1 / ell ^ 10) + 2 * S * (1 / H ^ 4) * ell))) / S

theorem computedRefinementError_lt (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) : computedRefinementError N nx < 1 / (inputSmallLog N : ℝ) := by
  have hcut : 64000000000000 ≤ inputSmallLog N := by
    have hsmall : 64000000000000 ≤ (2 : ℕ) ^ 46 := by norm_num
    exact hsmall.trans ((pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
      (by decide : 46 ≤ 1000)).trans hell)
  have hlarge : (64000000000000 : ℝ) ≤ inputSmallLog N := by exact_mod_cast hcut
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by linarith only [hlarge]
  have hpoly := inputHeight_polynomial_slack N hN hell
  have hroot := fourth_root_polynomial_slack hellone hpoly
    (Real.sqrt_nonneg _) (heightQuarterRoot_fourth_power N)
  have hHone : 1 ≤ inputHeight N := Nat.one_le_two_pow
  have hM : (integerParameters N).M ≤ inputHeight N :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hP : inputHeight N ^ 20 ≤ (integerParameters N).P :=
    pow_le_pow_right₀ hHone (by omega : 20 ≤ coarseExponent (inputSmallLog N) + 20)
  have hdepth := computed_tree_depth_bound N nx hN hnx ((by decide : 200 ≤ 64000000000000).trans hcut)
  have hcount := computed_refinement_count_exact N hN hell
  unfold computedRefinementError
  apply refinement_error_from_stage_bounds hlarge
  · exact (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans hpoly
  · exact (pow_le_pow_right₀ hellone (by decide : 4 ≤ 5000)).trans hroot
  · exact heightQuarterRoot_fourth_power N
  · have hp : (0 : ℝ) ≤ coarseExponent (inputSmallLog N) := Nat.cast_nonneg _
    linarith only [hp]
  · exact coarseExponent_shift_square _ ((by decide : 1764 ≤ 64000000000000).trans hcut)
  · exact_mod_cast hM
  · exact Nat.cast_nonneg _
  · exact_mod_cast hdepth
  · exact_mod_cast hP
  · exact (computed_warmup_count_root N).1
  · exact_mod_cast (computed_stage_positive_counts N hN hell).2
  · exact_mod_cast hcount

end EditApproximation

end OAI
