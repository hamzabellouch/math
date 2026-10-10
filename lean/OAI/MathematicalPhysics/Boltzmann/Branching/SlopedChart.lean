import OAI.MathematicalPhysics.Boltzmann.Branching.AffineSlices

namespace OAI

/-! # Chart estimates using a nonzero axial slope -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.AffineSlices

namespace BoltzmannNonuniqueness.SlopedChart

theorem weight_chart (q : ℝ) (v p : Velocity) (z s : ℝ) :
    W q (chart v p z s) = lineWeight q (direction (normal v p))
      (offset v p - slope v p * z) s := by
  unfold W singularity lineWeight
  rw [transverse_chart]

def rectangleFiber (q : ℝ) (v p : Velocity) (C D m S : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖normal v p‖⁻¹) * ∫⁻ z : ℝ,
    if |offset v p - slope v p * z - C| ≤ D then
      ∫⁻ s in Icc (m - S) (m + S), weightRatio q v (chart v p z s)
    else 0

theorem rectangleFiber_bound {q D S : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (v p : Velocity)
    (hn : normal v p ≠ 0) (ha : axial (v - p) ≠ 0) (C m : ℝ) :
    rectangleFiber q v p C D m S ≤
      ENNReal.ofReal (rectangleConstant q D S / (W q v * |axial (v - p)|)) := by
  have hnorm : 0 < ‖normal v p‖ := norm_pos_iff.mpr hn
  have hW := W_pos q v
  have hconst := rectangleConstant_nonneg hq₁ hq₂ hD hS
  have hB : slope v p ≠ 0 := div_ne_zero ha hnorm.ne'
  have hweight (z s : ℝ) : weightRatio q v (chart v p z s) =
      ENNReal.ofReal ((W q v)⁻¹) * ENNReal.ofReal
        (lineWeight q (direction (normal v p)) (offset v p - slope v p * z) s) := by
    unfold weightRatio
    rw [weight_chart, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (W q v)⁻¹)]
    apply congrArg ENNReal.ofReal
    simp only [div_eq_mul_inv, mul_comm]
  have hz (z : ℝ) :
      (if |offset v p - slope v p * z - C| ≤ D then
        ∫⁻ s in Icc (m - S) (m + S), weightRatio q v (chart v p z s) else 0) ≤
      ENNReal.ofReal ((W q v)⁻¹) *
        (if |offset v p - slope v p * z - C| ≤ D then
          ENNReal.ofReal (2 * S) + ENNReal.ofReal (AxialSlices.lineConstant q) *
            extendedPower q (offset v p - slope v p * z) else 0) := by
    by_cases h : |offset v p - slope v p * z - C| ≤ D
    · rw [ite_eq_left h, ite_eq_left h]
      simp_rw [hweight]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (lintegral_lineWeight_le_extended hq₁ hS _ (norm_direction hn) _ m)
    · simp only [ite_eq_right h, mul_zero, le_refl]
  unfold rectangleFiber
  apply (mul_le_mul' le_rfl (lintegral_mono hz)).trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hb := affine_rectangle_bound hq₁ hq₂ hD hS (offset v p) C hB
  apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl hb)).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (W q v)⁻¹),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ ‖normal v p‖⁻¹)]
  apply congrArg ENNReal.ofReal
  unfold PlaneChart.slope
  rw [abs_div, abs_of_pos hnorm]
  field_simp

theorem ball_coordinates {R : ℝ} (hR : 0 ≤ R) (v p : Velocity)
    (hn : normal v p ≠ 0) (z s : ℝ) (hb : ‖chart v p z s - v‖ ≤ R) :
    |offset v p - slope v p * z - inner ℝ (direction (normal v p)) (transverse v)| ≤ R ∧
      s ∈ Icc (inner ℝ (quarterTurn (direction (normal v p))) (transverse v) - R)
        (inner ℝ (quarterTurn (direction (normal v p))) (transverse v) + R) := by
  have he := norm_direction hn
  have hball : s ∈ ballLineRegion (direction (normal v p)) (transverse v)
      (offset v p - slope v p * z) z R := by
    rw [← sq_le_sq₀ (norm_nonneg _) hR, chart_displacement_norm_sq] at hb
    exact hb
  have hnorm : ‖line (direction (normal v p)) (offset v p - slope v p * z) s - transverse v‖ ≤ R := by
    change ‖line _ _ _ - _‖ ^ 2 + z ^ 2 ≤ R ^ 2 at hball
    nlinarith [sq_nonneg z, norm_nonneg (line (direction (normal v p))
      (offset v p - slope v p * z) s - transverse v)]
  constructor
  · have hi := abs_real_inner_le_norm (direction (normal v p))
      (line (direction (normal v p)) (offset v p - slope v p * z) s - transverse v)
    rw [inner_sub_right, inner_line _ _ _ he, he, one_mul] at hi
    exact hi.trans hnorm
  · exact ballLineRegion_subset_rectangle hR _ _ he _ _ hball

theorem ballChartFiber_le_rectangle {R : ℝ} (hR : 0 ≤ R) (q : ℝ) (v p : Velocity)
    (hn : normal v p ≠ 0) :
    ballChartFiber q v p R ≤ rectangleFiber q v p
      (inner ℝ (direction (normal v p)) (transverse v)) R
      (inner ℝ (quarterTurn (direction (normal v p))) (transverse v)) R := by
  unfold ballChartFiber rectangleFiber
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro z
  dsimp only
  by_cases hz : |offset v p - slope v p * z -
      inner ℝ (direction (normal v p)) (transverse v)| ≤ R
  · rw [ite_eq_left hz, ← lintegral_indicator measurableSet_Icc]
    apply lintegral_mono
    intro s
    dsimp only
    by_cases hb : ‖chart v p z s - v‖ ≤ R
    · rw [ite_eq_left hb, indicator_of_mem (ball_coordinates hR v p hn z s hb).2]
    · rw [ite_eq_right hb]
      exact bot_le
  · rw [ite_eq_right hz]
    have he : (∫⁻ s : ℝ, if ‖chart v p z s - v‖ ≤ R then weightRatio q v (chart v p z s) else 0) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      apply ae_of_all
      intro s
      have hb : ¬‖chart v p z s - v‖ ≤ R := fun h => hz (ball_coordinates hR v p hn z s h).1
      exact ite_eq_right hb
    exact le_of_eq he

theorem ballChartFiber_slope_bound {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 0 ≤ R) (v p : Velocity) (hn : normal v p ≠ 0) (ha : axial (v - p) ≠ 0) :
    ballChartFiber q v p R ≤
      ENNReal.ofReal (rectangleConstant q R R / (W q v * |axial (v - p)|)) :=
  (ballChartFiber_le_rectangle hR q v p hn).trans
    (rectangleFiber_bound hq₁ hq₂ hR hR v p hn ha _ _)

def smallFiber (q : ℝ) (v p : Velocity) (δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖normal v p‖⁻¹) * ∫⁻ z : ℝ, ∫⁻ s : ℝ,
    if ‖transverse (chart v p z s)‖ < δ then weightRatio q v (chart v p z s) else 0

theorem small_coordinates {δ : ℝ} (v p : Velocity)
    (hn : normal v p ≠ 0) (z s : ℝ) (h : ‖transverse (chart v p z s)‖ < δ) :
    |offset v p - slope v p * z| ≤ δ ∧ s ∈ Icc (-δ) δ := by
  rw [transverse_chart] at h
  have he := norm_direction hn
  have hsq := norm_line_sq (direction (normal v p)) (offset v p - slope v p * z) s he
  have hnorm := norm_nonneg (line (direction (normal v p)) (offset v p - slope v p * z) s)
  have hD : |offset v p - slope v p * z| ≤ δ := by
    nlinarith [sq_nonneg s, sq_abs (offset v p - slope v p * z),
      abs_nonneg (offset v p - slope v p * z)]
  have hs : |s| ≤ δ := by
    nlinarith [sq_nonneg (offset v p - slope v p * z), sq_abs s, abs_nonneg s]
  exact ⟨hD, abs_le.mp hs⟩

theorem smallFiber_le_rectangle (δ q : ℝ) (v p : Velocity)
    (hn : normal v p ≠ 0) :
    smallFiber q v p δ ≤ rectangleFiber q v p 0 δ 0 δ := by
  unfold smallFiber rectangleFiber
  simp only [sub_zero, zero_sub, zero_add]
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro z
  dsimp only
  by_cases hz : |offset v p - slope v p * z| ≤ δ
  · rw [ite_eq_left hz, ← lintegral_indicator measurableSet_Icc]
    apply lintegral_mono
    intro s
    dsimp only
    by_cases hs : ‖transverse (chart v p z s)‖ < δ
    · rw [ite_eq_left hs, indicator_of_mem (small_coordinates v p hn z s hs).2]
    · rw [ite_eq_right hs]
      exact bot_le
  · rw [ite_eq_right hz]
    have he : (∫⁻ s : ℝ, if ‖transverse (chart v p z s)‖ < δ then
        weightRatio q v (chart v p z s) else 0) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      apply ae_of_all
      intro s
      exact ite_eq_right (fun h => hz (small_coordinates v p hn z s h).1)
    exact le_of_eq he

theorem smallFiber_slope_bound {q δ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hδ : 0 ≤ δ) (v p : Velocity) (hn : normal v p ≠ 0) (ha : axial (v - p) ≠ 0) :
    smallFiber q v p δ ≤
      ENNReal.ofReal (rectangleConstant q δ δ / (W q v * |axial (v - p)|)) :=
  (smallFiber_le_rectangle δ q v p hn).trans
    (rectangleFiber_bound hq₁ hq₂ hδ hδ v p hn ha 0 0)

end BoltzmannNonuniqueness.SlopedChart

end

end OAI
