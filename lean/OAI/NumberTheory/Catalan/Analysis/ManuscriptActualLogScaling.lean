import OAI.NumberTheory.Catalan.Analysis.ManuscriptRealLogScaling
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOnePointLogInputs
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoBracketHeight
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section

namespace InternalCatalan.ManuscriptPrecision

def ComplexLogInputRange (z : ℂ) : Prop :=
  (2 / 125 : ℝ) ^ 4 ≤ z.re ^ 2 + z.im ^ 2 ∧
    z.re ^ 2 + z.im ^ 2 ≤ (248 / 125 : ℝ) ^ 4

private theorem range_of_norm_bounds {z : ℂ}
    (hl : (2 / 125 : ℝ) ^ 2 ≤ ‖z‖)
    (hu : ‖z‖ ≤ (248 / 125 : ℝ) ^ 2) : ComplexLogInputRange z := by
  unfold ComplexLogInputRange
  rw [barrierComplex_norm_sq]
  have hn := norm_nonneg z
  constructor
  · nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (2 / 125 : ℝ) ^ 2) hl]
  · nlinarith [mul_self_le_mul_self hn hu]

theorem linear_log_argument_range {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : ‖z‖ ≤ (123 / 125 : ℝ)) :
    ComplexLogInputRange (barrierTailLinearDen z x) := by
  have hl := Case2Height.linear_den_norm_lower (z := z) hx
  have hm : ‖(x : ℂ) * z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg z)
  have hu : ‖barrierTailLinearDen z x‖ ≤ 1 + ‖z‖ := by
    change ‖(1 : ℂ) - (x : ℂ) * z‖ ≤ 1 + ‖z‖
    have ht : ‖(1 : ℂ) - (x : ℂ) * z‖ ≤ 1 + ‖(x : ℂ) * z‖ := by
      simpa only [norm_one] using norm_sub_le (1 : ℂ) ((x : ℂ) * z)
    exact ht.trans (add_le_add le_rfl hm)
  apply range_of_norm_bounds <;> linarith

theorem quadratic_log_argument_range {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : ‖z‖ ≤ (123 / 125 : ℝ)) :
    ComplexLogInputRange (barrierTailQuadraticDen z x) := by
  have hn := norm_nonneg z
  have hz1 : ‖z‖ ≤ 1 := by linarith
  have hl := Case2Height.quadratic_den_norm_lower (z := z) hx hz1
  have hm : ‖(2 : ℂ) * (x : ℂ) * z‖ ≤ 2 * ‖z‖ := by
    calc
      _ = 2 * |x| * ‖z‖ := by norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hx hn]
  have hu : ‖barrierTailQuadraticDen z x‖ ≤ 1 + 2 * ‖z‖ + ‖z‖ ^ 2 := by
    calc
      _ ≤ ‖(1 : ℂ) - 2 * (x : ℂ) * z‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖(2 : ℂ) * (x : ℂ) * z‖) + ‖z ^ 2‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by
        rw [norm_one, norm_pow]
        exact add_le_add (add_le_add le_rfl hm) le_rfl
  apply range_of_norm_bounds
  · nlinarith [sq_nonneg (‖z‖ - 123 / 125)]
  · nlinarith [mul_self_le_mul_self hn hz]

theorem pair_log_argument_range {z w : ℂ}
    (hz : ‖z‖ ≤ (123 / 125 : ℝ)) (hw : ‖w‖ ≤ (123 / 125 : ℝ)) :
    ComplexLogInputRange (1 - z * w) := by
  have hmul : ‖z * w‖ ≤ (123 / 125 : ℝ) ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul hz hw (norm_nonneg w) (by norm_num)
  have hl : 1 - ‖z * w‖ ≤ ‖(1 : ℂ) - z * w‖ := by
    simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) (z * w)
  have hu : ‖(1 : ℂ) - z * w‖ ≤ 1 + ‖z * w‖ := by
    simpa only [norm_one] using norm_sub_le (1 : ℂ) (z * w)
  apply range_of_norm_bounds <;> linarith

theorem complex_log_input_power_range {z : ℂ} (h : ComplexLogInputRange z) :
    (2 : ℝ) ^ (-100 : ℤ) ≤ z.re ^ 2 + z.im ^ 2 ∧
    z.re ^ 2 + z.im ^ 2 ≤ (2 : ℝ) ^ (100 : ℤ) := by
  constructor
  · exact (by norm_num : (2 : ℝ) ^ (-100 : ℤ) ≤ (2 / 125 : ℝ) ^ 4).trans h.1
  · exact h.2.trans (by norm_num : (248 / 125 : ℝ) ^ 4 ≤ (2 : ℝ) ^ (100 : ℤ))

theorem actual_XP_log_argument_range {x : ℝ} (hx : |x| ≤ 1)
    {zr : ℂ × ℂ} (hzr : zr ∈ barrierP2Tail) :
    ComplexLogInputRange (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2) := by
  apply quadratic_log_argument_range hx
  exact (barrierP2_tail_norm_bounds zr hzr).1.trans (by norm_num)

theorem actual_XV_log_argument_range {x : ℝ} (hx : |x| ≤ 1)
    {zr : ℂ × ℂ} (hzr : zr ∈ barrierV2Tail) :
    ComplexLogInputRange (1 - (x : ℂ) * zr.1) := by
  apply linear_log_argument_range hx
  exact (barrierV2_tail_norm_bounds zr hzr).1.trans (by norm_num)

theorem actual_YV_log_argument_range {x : ℝ} (hx : |x| ≤ 1)
    {zr : ℂ × ℂ} (hzr : zr ∈ barrierV2Tail) :
    ComplexLogInputRange (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2) := by
  apply quadratic_log_argument_range hx
  exact (barrierV2_tail_norm_bounds zr hzr).1.trans (by norm_num)

theorem actual_P_norm_log_argument_range {zr ws : ℂ × ℂ}
    (hzr : zr ∈ barrierP2Tail) (hws : ws ∈ barrierP2Tail) :
    ComplexLogInputRange (1 - zr.1 * ws.1) := by
  apply pair_log_argument_range
  · exact (barrierP2_tail_norm_bounds zr hzr).1.trans (by norm_num)
  · exact (barrierP2_tail_norm_bounds ws hws).1.trans (by norm_num)

theorem actual_V_norm_log_argument_range {zr ws : ℂ × ℂ}
    (hzr : zr ∈ barrierV2Tail) (hws : ws ∈ barrierV2Tail) :
    ComplexLogInputRange (1 - zr.1 * ws.1) := by
  apply pair_log_argument_range
  · exact (barrierV2_tail_norm_bounds zr hzr).1.trans (by norm_num)
  · exact (barrierV2_tail_norm_bounds ws hws).1.trans (by norm_num)

def paperXPoints : List ℚ := Case2PointData.XPoints ++
  [Case1PointData.X0, Case1PointData.X1, Case1PointData.X2, Case1PointData.X3, Case1PointData.X4, Case1PointData.X5, Case1PointData.X6, Case1PointData.X7]

def paperYPoints : List ℚ := Case2PointData.YPoints ++
  [Case1PointData.Y0, Case1PointData.Y1, Case1PointData.Y2, Case1PointData.Y3, Case1PointData.Y4]

theorem paper_point_counts : paperXPoints.length = 27 ∧ paperYPoints.length = 23 := by
  norm_num [paperXPoints, paperYPoints, Case2PointData.XPoints, Case2PointData.YPoints]

theorem paper_X_point_margins : ∀ x ∈ paperXPoints,
    |(x : ℝ)| ≤ 1 ∧ (7 / 10000 : ℝ) ≤ |(x : ℝ)| ∧
      (7 / 10000 : ℝ) ≤ 1 - (x : ℝ) := by
  norm_num [paperXPoints, Case2PointData.XPoints, Case2PointData.X0, Case2PointData.X1, Case2PointData.X2, Case2PointData.X3, Case2PointData.X4, Case2PointData.X5, Case2PointData.X6, Case2PointData.X7, Case2PointData.X8, Case2PointData.X9, Case2PointData.X10, Case2PointData.X11, Case2PointData.X12, Case2PointData.X13, Case2PointData.X14, Case2PointData.X15, Case2PointData.X16, Case2PointData.X17, Case2PointData.X18, Case1PointData.X0, Case1PointData.X1, Case1PointData.X2, Case1PointData.X3, Case1PointData.X4, Case1PointData.X5, Case1PointData.X6, Case1PointData.X7]

theorem paper_Y_point_margins : ∀ x ∈ paperYPoints,
    (7 / 10000 : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1 - 7 / 10000 := by
  norm_num [paperYPoints, Case2PointData.YPoints, Case2PointData.Y0, Case2PointData.Y1, Case2PointData.Y2, Case2PointData.Y3, Case2PointData.Y4, Case2PointData.Y5, Case2PointData.Y6, Case2PointData.Y7, Case2PointData.Y8, Case2PointData.Y9, Case2PointData.Y10, Case2PointData.Y11, Case2PointData.Y12, Case2PointData.Y13, Case2PointData.Y14, Case2PointData.Y15, Case2PointData.Y16, Case2PointData.Y17, Case1PointData.Y0, Case1PointData.Y1, Case1PointData.Y2, Case1PointData.Y3, Case1PointData.Y4]

def XRealLogInputs (x : ℝ) : List ℝ := [|x|, 1 - x, 1 + x ^ 2]

def YRealLogInputs (x : ℝ) : List ℝ := [x, 1 - x]

theorem actual_X_real_log_input_range {x : ℚ} (hx : x ∈ paperXPoints)
    {s : ℝ} (hs : s ∈ XRealLogInputs (x : ℝ)) :
    s ∈ Set.Icc (7 / 10000 : ℝ) 2 := by
  obtain ⟨habs, hzero, hone⟩ := paper_X_point_margins x hx
  have hxx := abs_le.mp habs
  have hsq : (x : ℝ) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one (x : ℝ)).mpr habs
  simp only [XRealLogInputs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact ⟨hzero, habs.trans (by norm_num)⟩
  · exact ⟨hone, by linarith [hxx.1]⟩
  · constructor <;> nlinarith [sq_nonneg (x : ℝ)]

theorem actual_Y_real_log_input_range {x : ℚ} (hx : x ∈ paperYPoints)
    {s : ℝ} (hs : s ∈ YRealLogInputs (x : ℝ)) :
    s ∈ Set.Icc (7 / 10000 : ℝ) 2 := by
  obtain ⟨hzero, hone⟩ := paper_Y_point_margins x hx
  simp only [YRealLogInputs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨hzero, by linarith⟩
  · constructor <;> linarith

theorem real_log_input_power_range {s : ℝ} (h : s ∈ Set.Icc (7 / 10000 : ℝ) 2) :
    (2 : ℝ) ^ (-100 : ℤ) ≤ s ∧ s ≤ (2 : ℝ) ^ (100 : ℤ) := by
  constructor
  · exact (by norm_num : (2 : ℝ) ^ (-100 : ℤ) ≤ (7 / 10000 : ℝ)).trans h.1
  · exact h.2.trans (by norm_num : (2 : ℝ) ≤ (2 : ℝ) ^ (100 : ℤ))

theorem all_XP_point_log_input_ranges {x : ℚ} (hx : x ∈ Case2PointData.XPoints)
    {zr : ℂ × ℂ} (hzr : zr ∈ barrierP2Tail) :
    ComplexLogInputRange (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2) := by
  have hx' : x ∈ paperXPoints := List.mem_append.mpr (Or.inl hx)
  simpa only [Complex.ofReal_ratCast] using
    actual_XP_log_argument_range (paper_X_point_margins x hx').1 hzr

theorem all_XV_point_log_input_ranges {x : ℚ} (hx : x ∈ Case2PointData.XPoints)
    {zr : ℂ × ℂ} (hzr : zr ∈ barrierV2Tail) :
    ComplexLogInputRange (1 - (x : ℂ) * zr.1) := by
  have hx' : x ∈ paperXPoints := List.mem_append.mpr (Or.inl hx)
  simpa only [Complex.ofReal_ratCast] using
    actual_XV_log_argument_range (paper_X_point_margins x hx').1 hzr

theorem all_YV_point_log_input_ranges {x : ℚ} (hx : x ∈ Case2PointData.YPoints)
    {zr : ℂ × ℂ} (hzr : zr ∈ barrierV2Tail) :
    ComplexLogInputRange (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2) := by
  have hx' : x ∈ paperYPoints := List.mem_append.mpr (Or.inl hx)
  obtain ⟨hl, hu⟩ := paper_Y_point_margins x hx'
  have habs : |(x : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [Complex.ofReal_ratCast] using actual_YV_log_argument_range habs hzr

theorem actual_X_real_log_scaling {x : ℚ} (hx : x ∈ paperXPoints)
    (s : ℚ) (hs : (s : ℝ) ∈ XRealLogInputs (x : ℝ)) :
    ∃ m : ℤ, ∃ y : ℚ,
      (s : ℝ) = (2 : ℝ) ^ m * (y : ℝ) ∧
      (y : ℝ) ∈ Set.Icc (1 : ℝ) 2 ∧ |(m : ℝ)| ≤ 100 := by
  have h := real_log_input_power_range (actual_X_real_log_input_range hx hs)
  exact manuscript_rat_real_log_scaling s h.1 h.2

theorem actual_Y_real_log_scaling {x : ℚ} (hx : x ∈ paperYPoints)
    (s : ℚ) (hs : (s : ℝ) ∈ YRealLogInputs (x : ℝ)) :
    ∃ m : ℤ, ∃ y : ℚ,
      (s : ℝ) = (2 : ℝ) ^ m * (y : ℝ) ∧
      (y : ℝ) ∈ Set.Icc (1 : ℝ) 2 ∧ |(m : ℝ)| ≤ 100 := by
  have h := real_log_input_power_range (actual_Y_real_log_input_range hx hs)
  exact manuscript_rat_real_log_scaling s h.1 h.2

theorem complex_log_input_scaling {z : ℂ} (hz : ComplexLogInputRange z) :
    ∃ m : ℤ, ∃ y : ℝ,
      z.re ^ 2 + z.im ^ 2 = (2 : ℝ) ^ m * y ∧
      y ∈ Set.Icc (1 : ℝ) 2 ∧ |(m : ℝ)| ≤ 100 := by
  have h := complex_log_input_power_range hz
  exact manuscript_real_log_scaling (z.re ^ 2 + z.im ^ 2) h.1 h.2

theorem rational_complex_log_input_scaling (a b : ℚ)
    (hz : ComplexLogInputRange (barrierComplex a b)) :
    ∃ m : ℤ, ∃ y : ℚ,
      (barrierComplex a b).re ^ 2 + (barrierComplex a b).im ^ 2 =
        (2 : ℝ) ^ m * (y : ℝ) ∧
      (y : ℝ) ∈ Set.Icc (1 : ℝ) 2 ∧ |(m : ℝ)| ≤ 100 := by
  have h := complex_log_input_power_range hz
  have hlo : (2 : ℝ) ^ (-100 : ℤ) ≤ ((a ^ 2 + b ^ 2 : ℚ) : ℝ) := by
    simpa only [barrierComplex, Rat.cast_add, Rat.cast_pow] using h.1
  have hhi : ((a ^ 2 + b ^ 2 : ℚ) : ℝ) ≤ (2 : ℝ) ^ (100 : ℤ) := by
    simpa only [barrierComplex, Rat.cast_add, Rat.cast_pow] using h.2
  simpa only [barrierComplex, Rat.cast_add, Rat.cast_pow] using
    manuscript_rat_real_log_scaling (a ^ 2 + b ^ 2) hlo hhi

end InternalCatalan.ManuscriptPrecision

end

end OAI
