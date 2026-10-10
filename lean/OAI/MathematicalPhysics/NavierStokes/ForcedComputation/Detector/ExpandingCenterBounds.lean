import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingClockBounds

namespace OAI

/-! Positive derivatives of the gate centers. The constant starting
position disappears, so the estimate retains the reciprocal time scale. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows
open scoped ContDiff

theorem weight_derivative_bounds {C : ℝ} {m n : ℕ}
    (hC : ∀ i ≤ m, ∀ t, |iteratedDeriv i (smoothRamp 0 1) t| ≤ C)
    (hn : n ≤ m) (a T t : ℝ) :
    |iteratedDeriv n (firstWeight a T) t| ≤ |(T / 6)⁻¹| ^ n * C ∧
    |iteratedDeriv n (secondWeight a T) t| ≤ |(T / 6)⁻¹| ^ n * C ∧
    |iteratedDeriv n (thirdWeight a T) t| ≤ |(T / 6)⁻¹| ^ n * C := by
  have h₁ : a + T / 4 - (a + T / 12) = T / 6 := by ring
  have h₂ : a + 7 * T / 12 - (a + 5 * T / 12) = T / 6 := by ring
  have h₃ : a + 11 * T / 12 - (a + 3 * T / 4) = T / 6 := by ring
  refine ⟨?_, ?_, ?_⟩
  · simpa only [firstWeight, h₁] using
      smoothRamp_derivative_bound hC (a + T / 12) (a + T / 4) t hn
  · simpa only [secondWeight, h₂] using
      smoothRamp_derivative_bound hC (a + 5 * T / 12) (a + 7 * T / 12) t hn
  · simpa only [thirdWeight, h₃] using
      smoothRamp_derivative_bound hC (a + 3 * T / 4) (a + 11 * T / 12) t hn

theorem affine_clock_derivative_bound {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {n : ℕ} (hn : 0 < n) (c a b t δ : ℝ)
    (hfa : |iteratedDeriv n f t| ≤ δ) (hga : |iteratedDeriv n g t| ≤ δ) :
    |iteratedDeriv n (fun s => c + a * f s + b * g s) t| ≤
      (|a| + |b|) * δ := by
  have hfn : ContDiffAt ℝ n (fun s => a * f s) t :=
    (contDiff_const.mul hf).contDiffAt.of_le (by simp)
  have hgn : ContDiffAt ℝ n (fun s => b * g s) t :=
    (contDiff_const.mul hg).contDiffAt.of_le (by simp)
  have he : (fun s => c + a * f s + b * g s) =
      fun s => c + (a * f s + b * g s) := by funext s; ring
  rw [he, iteratedDeriv_const_add hn]
  change |iteratedDeriv n ((fun s => a * f s) + (fun s => b * g s)) t| ≤ _
  rw [iteratedDeriv_add hfn hgn, iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field]
  calc
    _ ≤ |a * iteratedDeriv n f t| + |b * iteratedDeriv n g t| := abs_add_le _ _
    _ = |a| * |iteratedDeriv n f t| + |b| * |iteratedDeriv n g t| := by
      rw [abs_mul, abs_mul]
    _ ≤ |a| * δ + |b| * δ := add_le_add
      (mul_le_mul_of_nonneg_left hfa (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hga (abs_nonneg _))
    _ = _ := by ring

theorem scheduledCenter_horizontal_jet {C : ℝ} {m n : ℕ}
    (hC : ∀ i ≤ m, ∀ t, |iteratedDeriv i (smoothRamp 0 1) t| ≤ C)
    (hn : 0 < n) (hnm : n ≤ m) (a T S S' t : ℝ)
    (k target : ℕ) (terminal : Bool) :
    |iteratedDeriv n (fun s => scheduledCenter a T S S' k target terminal s 0) t| ≤
      |S' * target - S * k| * (|(T / 6)⁻¹| ^ n * C) := by
  have he : (fun s => scheduledCenter a T S S' k target terminal s 0) =
      fun s => S * k + (S' * target - S * k) * secondWeight a T s := by
    funext s
    simp only [scheduledCenter, gateCenter, Matrix.cons_val_zero]
    ring
  rw [he, iteratedDeriv_const_add hn, iteratedDeriv_const_mul_field, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (weight_derivative_bounds hC hnm a T t).2.1 (abs_nonneg _)

theorem scheduledCenter_vertical_jet {C : ℝ} {m n : ℕ}
    (hC : ∀ i ≤ m, ∀ t, |iteratedDeriv i (smoothRamp 0 1) t| ≤ C)
    (hn : 0 < n) (hnm : n ≤ m) (a T S S' t : ℝ)
    (k target : ℕ) (terminal : Bool) :
    |iteratedDeriv n (fun s => scheduledCenter a T S S' k target terminal s 1) t| ≤
      (|-((k : ℝ) + 1) * S| + |((k : ℝ) + 2) * S + (if terminal then S' else -S')|) *
        (|(T / 6)⁻¹| ^ n * C) := by
  have he : (fun s => scheduledCenter a T S S' k target terminal s 1) =
      fun s => -S + (-((k : ℝ) + 1) * S) * firstWeight a T s +
        (((k : ℝ) + 2) * S + (if terminal then S' else -S')) * thirdWeight a T s := by
    funext s
    simp only [scheduledCenter, gateCenter, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  rw [he]
  exact affine_clock_derivative_bound (weights_smooth a T).1 (weights_smooth a T).2.2
    hn _ _ _ _ _ (weight_derivative_bounds hC hnm a T t).1
      (weight_derivative_bounds hC hnm a T t).2.2

end ForcedComputation.ExpandingDetector

end

end OAI
