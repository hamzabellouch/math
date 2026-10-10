import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! # Passing a bounded stationary error through a finite scalar shell

The comparison uses the original scalar functions and a pointwise remainder
bound. Square integrability of the approximating function supplies all the
integrability needed for the final error estimate.
-/

namespace Falconer
open Set MeasureTheory

theorem norm_sq_le_of_norm_sub_le {z w : ℂ} {ε : ℝ}
    (h : ‖z-w‖ ≤ ε) : ‖z‖^2 ≤ 2*‖w‖^2+2*ε^2 := by
  have hzw : ‖z‖ ≤ ‖w‖+ε := by
    calc
      ‖z‖ = ‖(z-w)+w‖ := by congr 1; ring
      _ ≤ ‖z-w‖+‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖+ε := by linarith
  have hs := pow_le_pow_left₀ (norm_nonneg z) hzw 2
  nlinarith [sq_nonneg (‖w‖-ε)]

theorem scalar_shell_error_transfer {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (F G : α → ℂ)
    (hF : Measurable F) (hG : Integrable (fun x => ‖G x‖^2) μ)
    {ε P H : ℝ} (hP : 0 ≤ P)
    (herr : ∀ᵐ x ∂μ, ‖F x-G x‖ ≤ ε)
    (hH : P*(∫ x, ‖G x‖^2 ∂μ) ≤ H) :
    Integrable (fun x => ‖F x‖^2) μ ∧
      P*(∫ x, ‖F x‖^2 ∂μ) ≤ 2*H+2*P*ε^2*μ.real univ := by
  have hb : ∀ᵐ x ∂μ, ‖F x‖^2 ≤ 2*‖G x‖^2+2*ε^2 :=
    herr.mono fun x hx => norm_sq_le_of_norm_sub_le hx
  have hupper : Integrable (fun x => 2*‖G x‖^2+2*ε^2) μ :=
    (hG.const_mul 2).add (integrable_const _)
  have hFi : Integrable (fun x => ‖F x‖^2) μ := by
    apply hupper.mono' (hF.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with x hx
    rwa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  refine ⟨hFi,?_⟩
  calc
    _ ≤ P*(∫ x, 2*‖G x‖^2+2*ε^2 ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hFi hupper hb) hP
    _ = 2*(P*(∫ x, ‖G x‖^2 ∂μ))+2*P*ε^2*μ.real univ := by
      rw [integral_add (hG.const_mul 2) (integrable_const _),integral_const_mul,
        integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := by linarith

end Falconer

end OAI
