import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {X Y : Ω → ℝ}

omit [IsFiniteMeasure μ] in

theorem condExp_div_const_ae (Y : Ω → ℝ) (c : ℝ) :
    μ[(fun ω => Y ω / c) | m] =ᵐ[μ] fun ω => μ[Y | m] ω / c := by
  have heq : (fun ω => Y ω / c) = c⁻¹ • Y := by
    ext ω
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  filter_upwards [condExp_smul (μ := μ) c⁻¹ Y m] with ω hω
  simpa only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using hω

theorem conditional_rescaled_increment_eq (hm : m ≤ mΩ)
    (hXm : StronglyMeasurable[m] X) (hX : Integrable X μ)
    (hY : Integrable Y μ) {a b : ℝ} (hb : b ≠ 0) :
    μ[(fun ω => Y ω / b - X ω / a) | m] =ᵐ[μ]
      fun ω => (μ[Y | m] ω - (b / a) * X ω) / b := by
  have hsub := condExp_sub (hY.div_const b) (hX.div_const a) m
  have hXdm : StronglyMeasurable[m] (fun ω => X ω / a) := by
    simpa only [div_eq_mul_inv] using hXm.mul_const a⁻¹
  have hXd := condExp_of_stronglyMeasurable hm hXdm (hX.div_const a)
  filter_upwards [hsub, condExp_div_const_ae (m := m) Y b] with ω hsubω hYω
  change μ[(fun ω => Y ω / b - X ω / a) | m] ω =
    μ[(fun ω => Y ω / b) | m] ω - μ[(fun ω => X ω / a) | m] ω at hsubω
  rw [hsubω, hYω, hXd]
  field_simp

theorem abs_conditional_rescaled_increment_le (hm : m ≤ mΩ)
    (hXm : StronglyMeasurable[m] X) (hX : Integrable X μ)
    (hY : Integrable Y μ) {a b ε : ℝ} (hb : 0 < b)
    (herror : ∀ᵐ ω ∂μ, |μ[Y | m] ω - (b / a) * X ω| ≤ ε) :
    ∀ᵐ ω ∂μ, |μ[(fun ω => Y ω / b - X ω / a) | m] ω| ≤ ε / b := by
  filter_upwards [conditional_rescaled_increment_eq hm hXm hX hY hb.ne', herror]
    with ω heq hle
  rw [heq, abs_div, abs_of_pos hb]
  exact div_le_div_of_nonneg_right hle hb.le

theorem conditional_rescaled_increment_le (hm : m ≤ mΩ)
    (hXm : StronglyMeasurable[m] X) (hX : Integrable X μ)
    (hY : Integrable Y μ) {a b ε : ℝ} (hb : 0 < b)
    (herror : ∀ᵐ ω ∂μ, μ[Y | m] ω - (b / a) * X ω ≤ ε) :
    ∀ᵐ ω ∂μ, μ[(fun ω => Y ω / b - X ω / a) | m] ω ≤ ε / b := by
  filter_upwards [conditional_rescaled_increment_eq hm hXm hX hY hb.ne', herror]
    with ω heq hle
  rw [heq]
  exact div_le_div_of_nonneg_right hle hb.le

theorem le_conditional_rescaled_increment (hm : m ≤ mΩ)
    (hXm : StronglyMeasurable[m] X) (hX : Integrable X μ)
    (hY : Integrable Y μ) {a b ε : ℝ} (hb : 0 < b)
    (herror : ∀ᵐ ω ∂μ, ε ≤ μ[Y | m] ω - (b / a) * X ω) :
    ∀ᵐ ω ∂μ, ε / b ≤ μ[(fun ω => Y ω / b - X ω / a) | m] ω := by
  filter_upwards [conditional_rescaled_increment_eq hm hXm hX hY hb.ne', herror]
    with ω heq hle
  rw [heq]
  exact div_le_div_of_nonneg_right hle hb.le

theorem conditional_rescaled_increment_eq_zero (hm : m ≤ mΩ)
    (hXm : StronglyMeasurable[m] X) (hX : Integrable X μ)
    (hY : Integrable Y μ) {a b : ℝ} (hb : b ≠ 0)
    (hmean : μ[Y | m] =ᵐ[μ] fun ω => (b / a) * X ω) :
    μ[(fun ω => Y ω / b - X ω / a) | m] =ᵐ[μ] 0 := by
  filter_upwards [conditional_rescaled_increment_eq hm hXm hX hY hb, hmean]
    with ω heq hmeanω
  simp only [Pi.zero_apply]
  rw [heq, hmeanω, sub_self, zero_div]

theorem rescaled_increment_identity {x y a b : ℝ} (hb : b ≠ 0) :
    y / b - x / a = ((y - x) + x * (1 - b / a)) / b := by
  field_simp
  ring

theorem abs_rescaled_increment_le
    {x y a b L Q δ smin : ℝ}
    (hjump : |y - x| ≤ L) (hx : |x| ≤ Q)
    (hscale : |1 - b / a| ≤ δ) (hsmin : 0 < smin) (hb : smin ≤ b) :
    |y / b - x / a| ≤ (L + Q * δ) / smin := by
  have hbpos : 0 < b := hsmin.trans_le hb
  have hL : 0 ≤ L := (abs_nonneg _).trans hjump
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hx
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hscale
  rw [rescaled_increment_identity hbpos.ne', abs_div, abs_of_pos hbpos]
  calc
    |y - x + x * (1 - b / a)| / b
        ≤ (|y - x| + |x| * |1 - b / a|) / b := by
          gcongr
          simpa only [abs_mul] using abs_add_le (y - x) (x * (1 - b / a))
    _ ≤ (L + Q * δ) / b := by gcongr
    _ ≤ (L + Q * δ) / smin :=
      div_le_div_of_nonneg_left (add_nonneg hL (mul_nonneg hQ hδ)) hsmin hb

omit [IsFiniteMeasure μ] in

theorem ae_abs_rescaled_increment_le
    {a b L Q δ smin : ℝ}
    (hjump : ∀ᵐ ω ∂μ, |Y ω - X ω| ≤ L)
    (hx : ∀ᵐ ω ∂μ, |X ω| ≤ Q)
    (hscale : |1 - b / a| ≤ δ) (hsmin : 0 < smin) (hb : smin ≤ b) :
    ∀ᵐ ω ∂μ, |Y ω / b - X ω / a| ≤ (L + Q * δ) / smin := by
  filter_upwards [hjump, hx] with ω hj hxω
  exact abs_rescaled_increment_le hj hxω hscale hsmin hb

end Balanced

end OAI
