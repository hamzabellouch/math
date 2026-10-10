import OAI.Probability.FreeIsing.Estimates.ExponentialTaylor

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem norm_integral_weighted_exp_remainder_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) (D : Ω → ℝ)
    (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ) :
    ‖∫ ω, Z ω * (Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
      (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2) ∂μ‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂μ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hD3.const_mul 4)
  filter_upwards [hZ] with ω hω
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
        (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2‖ :=
      mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    _ ≤ 4 * |D ω| ^ 3 := by
      simpa only [one_mul] using ExponentialTaylor.norm_exp_I_taylor_two_le (D ω)

theorem norm_integral_weighted_characteristic_step
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → ℂ) (D : Ω → ℝ) (h : ℝ)
    (hZm : AEStronglyMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hDm : Measurable D) (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hzero : ∫ ω, Z ω * (D ω : ℂ) ∂μ = 0) :
    ‖(∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
      (1 - (h : ℂ) / 2) * ∫ ω, Z ω ∂μ‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂μ +
        (1 / 2 : ℝ) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ‖ := by
  let R : Ω → ℂ := fun ω => Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
    (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2
  have hZint : Integrable Z μ :=
    (integrable_const (1 : ℝ)).mono' hZm hZ
  have hRm : Measurable R := by dsimp [R]; fun_prop
  have hRint : Integrable R μ := (hD3.const_mul 4).mono' hRm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ExponentialTaylor.norm_exp_I_taylor_two_le (D ω))
  have hZR : Integrable (fun ω => Z ω * R ω) μ := hRint.bdd_mul hZm hZ
  have hZD : Integrable (fun ω => Z ω * (D ω : ℂ)) μ :=
    hD.ofReal.bdd_mul hZm hZ
  have hZQ : Integrable (fun ω => Z ω * ((D ω : ℂ) ^ 2 - h)) μ := by
    have hq : Integrable (fun ω => (D ω : ℂ) ^ 2 - h) μ := by
      have hd2 : Integrable (fun ω => (D ω : ℂ) ^ 2) μ := by
        convert hD2.ofReal using 1
        funext ω
        exact (Complex.ofReal_pow (D ω) 2).symm
      exact hd2.sub (integrable_const (h : ℂ))
    exact hq.bdd_mul hZm hZ
  have hE : Integrable (fun ω => Z ω * Complex.exp ((D ω : ℂ) * Complex.I)) μ := by
    apply hZint.mul_bdd (c := 1)
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · exact Filter.Eventually.of_forall (fun ω => by simp)
  have halg : (fun ω => Z ω * Complex.exp ((D ω : ℂ) * Complex.I) -
      (1 - (h : ℂ) / 2) * Z ω) =
      (fun ω => Z ω * R ω + (Z ω * (D ω : ℂ)) * Complex.I -
        (Z ω * ((D ω : ℂ) ^ 2 - h)) * (1 / 2 : ℂ)) := by
    funext ω
    dsimp [R]
    ring
  have hid : (∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
      (1 - (h : ℂ) / 2) * ∫ ω, Z ω ∂μ =
      (∫ ω, Z ω * R ω ∂μ) -
        (∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ) * (1 / 2 : ℂ) := by
    rw [← integral_const_mul, ← integral_sub hE (hZint.const_mul _), halg]
    have hsum : Integrable (fun ω => Z ω * R ω + Z ω * (D ω : ℂ) * Complex.I) μ :=
      hZR.add (hZD.mul_const Complex.I)
    rw [integral_sub hsum (hZQ.mul_const (1 / 2 : ℂ)),
      integral_add hZR (hZD.mul_const Complex.I), integral_mul_const, integral_mul_const, hzero]
    simp
  rw [hid]
  calc
    _ ≤ ‖∫ ω, Z ω * R ω ∂μ‖ +
        ‖(∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ) * (1 / 2 : ℂ)‖ := norm_sub_le _ _
    _ ≤ (4 * ∫ ω, |D ω| ^ 3 ∂μ) +
        (1 / 2 : ℝ) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ‖ := by
      have hr := norm_integral_weighted_exp_remainder_le μ Z D hZ hD3
      have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [norm_mul, hn, mul_comm _ (1 / 2 : ℝ)]
      exact add_le_add hr le_rfl

theorem norm_gaussian_coefficient_sub_euler_le {h : ℝ}
    (h0 : 0 ≤ h) (h2 : h ≤ 2) :
    ‖Complex.exp (-(h : ℂ) / 2) - (1 - (h : ℂ) / 2)‖ ≤ h ^ 2 / 4 := by
  have hn : ‖-(h : ℂ) / 2‖ = h / 2 := by
    simp [Real.norm_eq_abs, abs_of_nonneg h0]
  have hb := Complex.norm_exp_sub_one_sub_id_le
    (x := -(h : ℂ) / 2) (by rw [hn]; linarith)
  rw [hn] at hb
  convert hb using 1 <;> congr 1 <;> ring

theorem norm_gaussian_coefficient_sub_euler_le_global {h : ℝ} (h0 : 0 ≤ h) :
    ‖Complex.exp (-(h : ℂ) / 2) - (1 - (h : ℂ) / 2)‖ ≤ h ^ 2 / 4 := by
  have hb := ExponentialTaylor.norm_exp_neg_sub_one_add_le_sq
    (show 0 ≤ h / 2 by positivity)
  convert hb using 1 <;> push_cast <;> congr 1 <;> ring_nf

theorem norm_integral_weighted_characteristic_gaussian_step_all
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℂ) (D : Ω → ℝ) {h : ℝ} (h0 : 0 ≤ h)
    (hZm : AEStronglyMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hDm : Measurable D) (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hzero : ∫ ω, Z ω * (D ω : ℂ) ∂μ = 0) :
    ‖(∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
      Complex.exp (-(h : ℂ) / 2) * ∫ ω, Z ω ∂μ‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂μ +
        (1 / 2 : ℝ) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ‖ + h ^ 2 / 4 := by
  have he := norm_integral_weighted_characteristic_step μ Z D h
    hZm hZ hDm hD hD2 hD3 hzero
  have hZi : ‖∫ ω, Z ω ∂μ‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) hZ
  have hc : ‖(1 - (h : ℂ) / 2) - Complex.exp (-(h : ℂ) / 2)‖ ≤ h ^ 2 / 4 := by
    rw [norm_sub_rev]
    exact norm_gaussian_coefficient_sub_euler_le_global h0
  have halg : (∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
        Complex.exp (-(h : ℂ) / 2) * ∫ ω, Z ω ∂μ =
      ((∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
        (1 - (h : ℂ) / 2) * ∫ ω, Z ω ∂μ) +
      ((1 - (h : ℂ) / 2) - Complex.exp (-(h : ℂ) / 2)) * ∫ ω, Z ω ∂μ := by ring
  rw [halg]
  apply (norm_add_le _ _).trans
  apply add_le_add he
  rw [norm_mul]
  calc
    _ ≤ ‖(1 - (h : ℂ) / 2) - Complex.exp (-(h : ℂ) / 2)‖ * 1 :=
      mul_le_mul_of_nonneg_left hZi (norm_nonneg _)
    _ ≤ h ^ 2 / 4 := by simpa only [mul_one] using hc

theorem norm_integral_weighted_characteristic_gaussian_step
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℂ) (D : Ω → ℝ) {h : ℝ} (h0 : 0 ≤ h) (_h2 : h ≤ 2)
    (hZm : AEStronglyMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hDm : Measurable D) (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hzero : ∫ ω, Z ω * (D ω : ℂ) ∂μ = 0) :
    ‖(∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
      Complex.exp (-(h : ℂ) / 2) * ∫ ω, Z ω ∂μ‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂μ +
        (1 / 2 : ℝ) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ‖ + h ^ 2 / 4 :=
  norm_integral_weighted_characteristic_gaussian_step_all μ Z D h0
    hZm hZ hDm hD hD2 hD3 hzero

theorem norm_integral_weighted_characteristic_gaussian_step_all_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℂ) (D : Ω → ℝ) (u : ℝ) {v : ℝ}
    (hv : 0 ≤ v)
    (hZm : AEStronglyMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hDm : Measurable D) (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hzero : ∫ ω, Z ω * (D ω : ℂ) ∂μ = 0) :
    ‖(∫ ω, Z ω * Complex.exp (((u * D ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      Complex.exp (-((u ^ 2 * v : ℝ) : ℂ) / 2) * ∫ ω, Z ω ∂μ‖ ≤
      4 * |u| ^ 3 * (∫ ω, |D ω| ^ 3 ∂μ) +
        (u ^ 2 / 2) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - v) ∂μ‖ +
        u ^ 4 * v ^ 2 / 4 := by
  have hs2 : Integrable (fun ω => (u * D ω) ^ 2) μ := by
    simpa only [mul_pow] using hD2.const_mul (u ^ 2)
  have hs3 : Integrable (fun ω => |u * D ω| ^ 3) μ := by
    simpa only [abs_mul, mul_pow] using hD3.const_mul (|u| ^ 3)
  have hsz : ∫ ω, Z ω * ((u * D ω : ℝ) : ℂ) ∂μ = 0 := by
    calc
      _ = (u : ℂ) * ∫ ω, Z ω * (D ω : ℂ) ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        push_cast
        ring
      _ = 0 := by rw [hzero, mul_zero]
  have hs := norm_integral_weighted_characteristic_gaussian_step_all μ Z
    (fun ω => u * D ω) (mul_nonneg (sq_nonneg u) hv)
    hZm hZ (hDm.const_mul u) (hD.const_mul u) hs2 hs3 hsz
  have hthird : (∫ ω, |u * D ω| ^ 3 ∂μ) =
      |u| ^ 3 * ∫ ω, |D ω| ^ 3 ∂μ := by
    simp only [abs_mul, mul_pow, integral_const_mul]
  have hquad : (∫ ω, Z ω * (((u * D ω : ℝ) : ℂ) ^ 2 - (u ^ 2 * v : ℝ)) ∂μ) =
      (u : ℂ) ^ 2 * ∫ ω, Z ω * ((D ω : ℂ) ^ 2 - v) ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext ω
    push_cast
    ring
  rw [hthird, hquad, norm_mul] at hs
  have hn : ‖(u : ℂ) ^ 2‖ = u ^ 2 := by simp [norm_pow, sq_abs]
  rw [hn] at hs
  convert hs using 1
  ring

theorem norm_integral_weighted_characteristic_gaussian_step_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℂ) (D : Ω → ℝ) (u : ℝ) {v : ℝ}
    (hv : 0 ≤ v) (_huv : u ^ 2 * v ≤ 2)
    (hZm : AEStronglyMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hDm : Measurable D) (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hzero : ∫ ω, Z ω * (D ω : ℂ) ∂μ = 0) :
    ‖(∫ ω, Z ω * Complex.exp (((u * D ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      Complex.exp (-((u ^ 2 * v : ℝ) : ℂ) / 2) * ∫ ω, Z ω ∂μ‖ ≤
      4 * |u| ^ 3 * (∫ ω, |D ω| ^ 3 ∂μ) +
        (u ^ 2 / 2) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - v) ∂μ‖ +
        u ^ 4 * v ^ 2 / 4 :=
  norm_integral_weighted_characteristic_gaussian_step_all_mul μ Z D u hv
    hZm hZ hDm hD hD2 hD3 hzero

end Problem367

end

end OAI
