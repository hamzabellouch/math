import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import OAI.Analysis.IrrationalRotation.Analysis.ExponentialDecay

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace InvariantProjection.FieldPowerBounds

variable {X E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {μ : Measure X}

theorem ae_pow_apply (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ⇑(T ξ) =ᵐ[μ] fun x => A x (ξ x))
    (n : ℕ) (ξ : Lp E 2 μ) :
    ⇑((T ^ n) ξ) =ᵐ[μ] fun x => (A x ^ n) (ξ x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [hT ((T ^ n) ξ), ih] with x hx hix
    rw [hx, hix, pow_succ', mul_apply_eq_comp]

theorem norm_pow_le (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ⇑(T ξ) =ᵐ[μ] fun x => A x (ξ x))
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (hA : ∀ᵐ x ∂μ, ‖A x ^ n‖ ≤ B) :
    ‖T ^ n‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro ξ
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ae_pow_apply T A hT n ξ, hA] with x hx hAx
  rw [hx]
  exact ((A x ^ n).le_opNorm (ξ x)).trans
    (mul_le_mul_of_nonneg_right hAx (norm_nonneg _))

theorem all_rates_norm_decay (T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ⇑(T ξ) =ᵐ[μ] fun x => A x (ξ x))
    (hA : ∀ a : ℝ, 0 < a → ∀ᶠ (n : ℕ) in atTop,
      ∀ᵐ x ∂μ, ‖A x ^ n‖ ≤ Real.exp (-a * n)) :
    ∀ a : ℝ, 0 < a → ∀ᶠ (n : ℕ) in atTop,
      ‖T ^ n‖ ≤ Real.exp (-a * n) := by
  intro a ha
  filter_upwards [hA a ha] with n hn
  exact norm_pow_le T A hT n (Real.exp_nonneg _) hn

theorem norm_quasinilpotent (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ⇑(T ξ) =ᵐ[μ] fun x => A x (ξ x))
    (hA : ∀ a : ℝ, 0 < a → ∀ᶠ (n : ℕ) in atTop,
      ∀ᵐ x ∂μ, ‖A x ^ n‖ ≤ Real.exp (-a * n)) :
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) :=
  Invariant233.norm_quasinilpotent_of_exponential_decay T (all_rates_norm_decay T A hT hA)

end InvariantProjection.FieldPowerBounds

end

end OAI
