import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

/-! # Logarithmic bounds for a probability exponential integral -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem exponential_integral_log_bounds {F : X → ℝ} {ε A B : ℝ} {S : Set X}
    (hε : 0 < ε) (hS0 : 0 < μ.real S)
    (hi : Integrable (fun x => Real.exp (F x/ε)) μ)
    (hlo : ∀ᵐ x ∂μ.restrict S, A ≤ F x) (hup : ∀ᵐ x ∂μ, F x ≤ B) :
    0 < (∫ x, Real.exp (F x/ε) ∂μ) ∧
      A+ε*Real.log (μ.real S) ≤ ε*Real.log (∫ x, Real.exp (F x/ε) ∂μ) ∧
      ε*Real.log (∫ x, Real.exp (F x/ε) ∂μ) ≤ B := by
  have hl : μ.real S*Real.exp (A/ε) ≤ ∫ x, Real.exp (F x/ε) ∂μ := by
    calc
      _ = ∫ x in S, Real.exp (A/ε) ∂μ := by simp
      _ ≤ ∫ x in S, Real.exp (F x/ε) ∂μ :=
        integral_mono_ae (integrable_const _) hi.integrableOn (hlo.mono fun x hx =>
          Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx hε.le))
      _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall fun x => (Real.exp_pos _).le)
  have hu : (∫ x, Real.exp (F x/ε) ∂μ) ≤ Real.exp (B/ε) := by
    calc
      _ ≤ ∫ x, Real.exp (B/ε) ∂μ := integral_mono_ae hi (integrable_const _)
        (hup.mono fun x hx => Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx hε.le))
      _ = _ := by simp
  have hp : 0 < (∫ x, Real.exp (F x/ε) ∂μ) := (mul_pos hS0 (Real.exp_pos _)).trans_le hl
  refine ⟨hp,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (Real.log_le_log (mul_pos hS0 (Real.exp_pos _)) hl) hε.le
    rw [Real.log_mul hS0.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
    have he : ε*(Real.log (μ.real S)+A/ε) = A+ε*Real.log (μ.real S) := by
      field_simp
      ring
    rwa [he] at hh
  · have hh := mul_le_mul_of_nonneg_left (Real.log_le_log hp hu) hε.le
    rw [Real.log_exp] at hh
    simpa only [mul_div_cancel₀ _ hε.ne'] using hh

end RegularPointCoordinates

end

end OAI
