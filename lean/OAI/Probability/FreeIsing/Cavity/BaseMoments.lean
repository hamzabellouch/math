import OAI.Probability.FreeIsing.Gaussian.Moments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem abs_le_cosh_mul_abs_tanh {y R : ℝ} (hR : 0 ≤ R) (hy : |y| ≤ R) :
    |y| ≤ Real.cosh R * |Real.tanh y| := by
  calc
    |y| ≤ Real.sinh |y| := Real.self_le_sinh_iff.mpr (abs_nonneg y)
    _ = |Real.sinh y| := (Real.abs_sinh y).symm
    _ = Real.cosh y * |Real.tanh y| := by
      rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos y)]
      field_simp
    _ ≤ Real.cosh R * |Real.tanh y| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg hR] using hy)

theorem sq_le_tanh_sq_add_fourth {y x B : ℝ} (hB : 0 ≤ B) (hyx : |y - x| ≤ B) :
    y ^ 2 ≤ Real.cosh (B + 1) ^ 2 * Real.tanh y ^ 2 +
      2 * (1 + B ^ 2) * |x| ^ 4 := by
  by_cases hx : |x| ≤ 1
  · have hy : |y| ≤ B + 1 := by
      calc
        |y| = |y - x + x| := by congr 1; ring
        _ ≤ |y - x| + |x| := abs_add_le _ _
        _ ≤ B + 1 := add_le_add hyx hx
    have hs := pow_le_pow_left₀ (abs_nonneg y)
      (abs_le_cosh_mul_abs_tanh (by linarith : 0 ≤ B + 1) hy) 2
    simp only [mul_pow, sq_abs] at hs
    exact hs.trans (le_add_of_nonneg_right (by positivity))
  · have hx1 : 1 < |x| := lt_of_not_ge hx
    have hx2 : 1 ≤ |x| ^ 2 := by nlinarith
    have hx4 : |x| ^ 2 ≤ |x| ^ 4 := by nlinarith [sq_nonneg (|x| ^ 2 - 1)]
    have hdiff := pow_le_pow_left₀ (abs_nonneg (y - x)) hyx 2
    simp only [sq_abs] at hdiff
    have hY : y ^ 2 ≤ 2 * B ^ 2 + 2 * x ^ 2 := by nlinarith [sq_nonneg (y - 2 * x)]
    have hB4 : B ^ 2 ≤ B ^ 2 * |x| ^ 4 := by
      simpa using mul_le_mul_of_nonneg_left (hx2.trans hx4) (sq_nonneg B)
    have hmain : y ^ 2 ≤ 2 * (1 + B ^ 2) * |x| ^ 4 := by
      nlinarith [sq_abs x]
    exact hmain.trans (le_add_of_nonneg_left (by positivity))

theorem integrable_tanh_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ) :
    Integrable (fun ω => Real.tanh (Y ω) ^ 2) μ := by
  have hm : AEMeasurable (fun ω => Real.tanh (Y ω)) μ := by
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    exact (Real.continuous_sinh.measurable.comp_aemeasurable hY).div
      (Real.continuous_cosh.measurable.comp_aemeasurable hY)
  apply (integrable_const (1 : ℝ)).mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.tanh (Y ω)))]
  exact (Real.tanh_sq_lt_one (Y ω)).le

theorem integral_sq_le_tanh_sq_add_fourth {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y X : Ω → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hY : AEMeasurable Y μ)
    (hX4 : Integrable (fun ω => |X ω| ^ 4) μ)
    (hbound : ∀ᵐ ω ∂μ, |Y ω - X ω| ≤ B) :
    Integrable (fun ω => Y ω ^ 2) μ ∧
    (∫ ω, Y ω ^ 2 ∂μ) ≤ Real.cosh (B + 1) ^ 2 * (∫ ω, Real.tanh (Y ω) ^ 2 ∂μ) +
      2 * (1 + B ^ 2) * (∫ ω, |X ω| ^ 4 ∂μ) := by
  have hT := integrable_tanh_sq hY
  have hdom := (hT.const_mul (Real.cosh (B + 1) ^ 2)).add
    (hX4.const_mul (2 * (1 + B ^ 2)))
  have hle : ∀ᵐ ω ∂μ, Y ω ^ 2 ≤
      Real.cosh (B + 1) ^ 2 * Real.tanh (Y ω) ^ 2 +
        2 * (1 + B ^ 2) * |X ω| ^ 4 := by
    filter_upwards [hbound] with ω hω
    exact sq_le_tanh_sq_add_fourth hB hω
  have hint : Integrable (fun ω => Y ω ^ 2) μ := by
    apply hdom.mono' (hY.pow_const 2).aestronglyMeasurable
    filter_upwards [hle] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y ω)), Pi.add_apply] using hω
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, Y ω ^ 2 ∂μ) ≤ ∫ ω,
        Real.cosh (B + 1) ^ 2 * Real.tanh (Y ω) ^ 2 +
          2 * (1 + B ^ 2) * |X ω| ^ 4 ∂μ := integral_mono_ae hint hdom hle
    _ = _ := by rw [integral_add (hT.const_mul _) (hX4.const_mul _), integral_const_mul,
      integral_const_mul]

theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) (hY2 : Integrable (fun ω => Y ω ^ 2) μ) :
    (∫ ω, |Y ω| ∂μ) ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
  have hm : MemLp Y 2 μ := (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mpr hY2
  have hma : MemLp (fun ω => |Y ω|) 2 μ := by simpa only [Real.norm_eq_abs] using hm.norm
  have hv := variance_nonneg (fun ω => |Y ω|) μ
  rw [variance_eq_sub hma] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  exact Real.le_sqrt_of_sq_le (by linarith)

theorem integrable_abs_pow_of_bounded_perturbation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y X : Ω → ℝ} {B : ℝ} (p : ℕ)
    (hB : 0 ≤ B) (hY : AEMeasurable Y μ)
    (hX : Integrable (fun ω => |X ω| ^ p) μ)
    (hbound : ∀ᵐ ω ∂μ, |Y ω - X ω| ≤ B) :
    Integrable (fun ω => |Y ω| ^ p) μ := by
  apply ((hX.add (integrable_const (B ^ p))).const_mul (2 ^ (p - 1) : ℝ)).mono'
    (hY.abs.pow_const p).aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  change ‖|Y ω| ^ p‖ ≤ 2 ^ (p - 1) * (|X ω| ^ p + B ^ p)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p)]
  have hsum : |Y ω| ≤ |X ω| + B := by
    have htriangle := abs_add_le (Y ω - X ω) (X ω)
    have heq : Y ω - X ω + X ω = Y ω := by ring
    rw [heq] at htriangle
    linarith
  exact (pow_le_pow_left₀ (abs_nonneg _) hsum p).trans (add_pow_le (abs_nonneg _) hB p)

theorem integrable_cavity_abs_pow_of_gaussian_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {G Y : Ω → ℝ} {B t : ℝ}
    (hG : HasLaw G (gaussianReal 0 1) μ) (hY : AEMeasurable Y μ)
    (hB : 0 ≤ B) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hbound : ∀ᵐ ω ∂μ, |Y ω - (t + Real.sqrt t * G ω)| ≤ B) (p : ℕ) :
    Integrable (fun ω => |Y ω| ^ p) μ :=
  integrable_abs_pow_of_bounded_perturbation p hB hY
    (integrable_gaussian_observation_abs_pow_of_hasLaw hG ht ht1 p) hbound

def cavityBaseConstant (B C : ℝ) : ℝ :=
  Real.cosh (B + 1) ^ 2 * C + 2 * (1 + B ^ 2) * Real.exp 32

theorem cavityBaseConstant_pos {B C : ℝ} (hC : 0 ≤ C) :
    0 < cavityBaseConstant B C := by
  unfold cavityBaseConstant
  positivity

theorem cavity_base_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {G Y : Ω → ℝ} {B C t : ℝ}
    (hG : HasLaw G (gaussianReal 0 1) μ) (hY : AEMeasurable Y μ)
    (hB : 0 ≤ B) (ht : 0 < t) (ht1 : t ≤ 1)
    (hbound : ∀ᵐ ω ∂μ, |Y ω - (t + Real.sqrt t * G ω)| ≤ B)
    (hinfo : (∫ ω, Real.tanh (Y ω) ^ 2 ∂μ) ≤ C * Real.sqrt t) :
    Integrable (fun ω => Y ω ^ 2) μ ∧
      (∫ ω, Y ω ^ 2 ∂μ) ≤ cavityBaseConstant B C * Real.sqrt t := by
  have hX4 := integrable_gaussian_observation_abs_pow_of_hasLaw hG ht.le ht1 4
  have hX4bound := integral_gaussian_observation_abs_pow_le_of_hasLaw
    hG (p := 4) ht ht1 (by decide)
  norm_num at hX4bound
  obtain ⟨hint, hsecond⟩ := integral_sq_le_tanh_sq_add_fourth hB hY hX4 hbound
  refine ⟨hint, hsecond.trans ?_⟩
  calc
    Real.cosh (B + 1) ^ 2 * (∫ ω, Real.tanh (Y ω) ^ 2 ∂μ) +
        2 * (1 + B ^ 2) * (∫ ω, |t + Real.sqrt t * G ω| ^ 4 ∂μ) ≤
      Real.cosh (B + 1) ^ 2 * (C * Real.sqrt t) +
        2 * (1 + B ^ 2) * (Real.exp 32 * t) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hinfo (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hX4bound (by positivity))
    _ = Real.cosh (B + 1) ^ 2 * C * Real.sqrt t +
        (2 * (1 + B ^ 2) * Real.exp 32) * t := by ring
    _ ≤ Real.cosh (B + 1) ^ 2 * C * Real.sqrt t +
        (2 * (1 + B ^ 2) * Real.exp 32) * Real.sqrt t := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.le_sqrt_self_iff.mpr ht1) (by positivity))
    _ = cavityBaseConstant B C * Real.sqrt t := by unfold cavityBaseConstant; ring

theorem cavity_base_first_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {G Y : Ω → ℝ} {B C t : ℝ}
    (hG : HasLaw G (gaussianReal 0 1) μ) (hY : AEMeasurable Y μ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1)
    (hbound : ∀ᵐ ω ∂μ, |Y ω - (t + Real.sqrt t * G ω)| ≤ B)
    (hinfo : (∫ ω, Real.tanh (Y ω) ^ 2 ∂μ) ≤ C * Real.sqrt t) :
    (∫ ω, |Y ω| ∂μ) ≤ Real.sqrt (cavityBaseConstant B C) * t ^ (1 / 4 : ℝ) := by
  obtain ⟨hint, hsecond⟩ := cavity_base_second_moment hG hY hB ht ht1 hbound hinfo
  have hquarter : Real.sqrt (Real.sqrt t) = t ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    norm_num
  calc
    (∫ ω, |Y ω| ∂μ) ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) :=
      integral_abs_le_sqrt_integral_sq hY hint
    _ ≤ Real.sqrt (cavityBaseConstant B C * Real.sqrt t) :=
      Real.sqrt_le_sqrt hsecond
    _ = Real.sqrt (cavityBaseConstant B C) * t ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_mul (cavityBaseConstant_pos hC).le, hquarter]

end Problem367

end

end OAI
