import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CenterPaths
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PulseBounds

namespace OAI

noncomputable section
namespace VelocityDetection.CenterPaths
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open SmoothProfiles

theorem iteratedDeriv_theta (a T : ℝ) (j m : ℕ) (t : ℝ) :
    iteratedDeriv m (theta a T j) t = (6 / T) ^ m *
      iteratedDeriv m step (2 * (3 * (t - a) / T - j) - 1 / 2) := by
  have heq : theta a T j = fun t => step ((6 / T) * t + (-6 * a / T - 2 * j - 1 / 2)) := by
    funext t
    dsimp [theta, ramp]
    congr 1
    ring
  rw [heq, iteratedDeriv_affine Real.smoothTransition.contDiff]
  have heqarg : (6 / T) * t + (-6 * a / T - 2 * j - 1 / 2) =
      2 * (3 * (t - a) / T - j) - 1 / 2 := by ring
  dsimp only
  rw [heqarg]

theorem center_horizontal_affine (a T S S' σ : ℝ) (k l : ℕ) (t : ℝ) :
    center a T S S' σ k l t 0 = S * k + (S' * l - S * k) * theta a T 1 t := by
  simp only [center, Matrix.cons_val_zero]
  ring

theorem center_vertical_affine (a T S S' σ : ℝ) (k l : ℕ) (t : ℝ) :
    center a T S S' σ k l t 1 = -S +
      ((privateRow S k + S) * theta a T 0 t + (σ * S' - privateRow S k) * theta a T 2 t) := by
  simp [center]
  ring

theorem iteratedDeriv_center_horizontal (a T S S' σ : ℝ) (k l m : ℕ) (t : ℝ) :
    iteratedDeriv (m + 1) (fun s => center a T S S' σ k l s 0) t =
      (S' * l - S * k) * iteratedDeriv (m + 1) (theta a T 1) t := by
  have heq : (fun s => center a T S S' σ k l s 0) =
      fun s => S * k + (S' * l - S * k) * theta a T 1 s :=
    funext (center_horizontal_affine a T S S' σ k l)
  rw [heq, iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field]

theorem iteratedDeriv_center_vertical (a T S S' σ : ℝ) (k l m : ℕ) (t : ℝ) :
    iteratedDeriv (m + 1) (fun s => center a T S S' σ k l s 1) t =
      (privateRow S k + S) * iteratedDeriv (m + 1) (theta a T 0) t +
      (σ * S' - privateRow S k) * iteratedDeriv (m + 1) (theta a T 2) t := by
  have heq : (fun s => center a T S S' σ k l s 1) =
      fun s => -S + ((privateRow S k + S) * theta a T 0 s +
        (σ * S' - privateRow S k) * theta a T 2 s) :=
    funext (center_vertical_affine a T S S' σ k l)
  rw [heq, iteratedDeriv_const_add (by omega)]
  have h₀ : ContDiff ℝ (m + 1 : ℕ) (fun s => (privateRow S k + S) * theta a T 0 s) :=
    (contDiff_infty.mp (by fun_prop : ContDiff ℝ ∞ _) (m + 1))
  have h₂ : ContDiff ℝ (m + 1 : ℕ) (fun s => (σ * S' - privateRow S k) * theta a T 2 s) :=
    (contDiff_infty.mp (by fun_prop : ContDiff ℝ ∞ _) (m + 1))
  rw [iteratedDeriv_fun_add h₀.contDiffAt h₂.contDiffAt,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]

theorem theta_derivative_bound (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (a T : ℝ) (_ : 0 < T) (j : ℕ) (t : ℝ),
      |iteratedDeriv (m + 1) (theta a T j) t| ≤ B / T ^ (m + 1) := by
  obtain ⟨B, hB, hBound⟩ := positive_derivatives_bounded m
  refine ⟨6 ^ (m + 1) * B, by positivity, fun a T hT j t => ?_⟩
  rw [iteratedDeriv_theta, abs_mul, abs_pow, abs_of_pos (by positivity : 0 < 6 / T)]
  calc
    _ ≤ (6 / T) ^ (m + 1) * B :=
      mul_le_mul_of_nonneg_left (hBound _) (by positivity)
    _ = _ := by rw [div_pow]; ring

theorem center_derivative_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a T S S' σ : ℝ) (k l : ℕ), 0 < T →
      |S| ≤ T → |S * k| ≤ T → |S' * l| ≤ T → |privateRow S k| ≤ T → |σ * S'| ≤ T →
      ∀ (t : ℝ) (i : Fin 2),
        |iteratedDeriv (m + 1) (fun s => center a T S S' σ k l s i) t| ≤ C / T ^ m := by
  obtain ⟨B, hB, hBound⟩ := theta_derivative_bound m
  refine ⟨4 * B, by positivity, ?_⟩
  intro a T S S' σ k l hT hS hSk hSl hY hσ t i
  have hnum : 0 ≤ B / T ^ (m + 1) := by positivity
  have hcoef₀ : |S' * l - S * k| ≤ 2 * T := by
    calc
      _ ≤ |S' * l| + |S * k| := abs_sub _ _
      _ ≤ _ := by linarith
  have hcoef₁ : |privateRow S k + S| ≤ 2 * T := by
    calc
      _ ≤ |privateRow S k| + |S| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hcoef₂ : |σ * S' - privateRow S k| ≤ 2 * T := by
    calc
      _ ≤ |σ * S'| + |privateRow S k| := abs_sub _ _
      _ ≤ _ := by linarith
  have hscale : 4 * T * (B / T ^ (m + 1)) = 4 * B / T ^ m := by
    rw [pow_succ]
    field_simp
  fin_cases i
  · change |iteratedDeriv (m + 1) (fun s => center a T S S' σ k l s 0) t| ≤ _
    rw [iteratedDeriv_center_horizontal, abs_mul]
    calc
      _ ≤ (2 * T) * (B / T ^ (m + 1)) :=
        mul_le_mul hcoef₀ (hBound a T hT 1 t) (abs_nonneg _) (by positivity)
      _ ≤ 4 * T * (B / T ^ (m + 1)) := by nlinarith
      _ = _ := hscale
  · change |iteratedDeriv (m + 1) (fun s => center a T S S' σ k l s 1) t| ≤ _
    rw [iteratedDeriv_center_vertical]
    calc
      _ ≤ |(privateRow S k + S) * iteratedDeriv (m + 1) (theta a T 0) t| +
          |(σ * S' - privateRow S k) * iteratedDeriv (m + 1) (theta a T 2) t| := abs_add_le _ _
      _ ≤ (2 * T) * (B / T ^ (m + 1)) + (2 * T) * (B / T ^ (m + 1)) := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul hcoef₁ (hBound a T hT 0 t) (abs_nonneg _) (by positivity))
          (mul_le_mul hcoef₂ (hBound a T hT 2 t) (abs_nonneg _) (by positivity))
      _ = _ := by linarith [hscale]

end VelocityDetection.CenterPaths
end

end OAI
