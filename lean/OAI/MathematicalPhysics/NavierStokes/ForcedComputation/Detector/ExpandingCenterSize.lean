import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingTimeJetBounds

namespace OAI

/-! Uniform address dependence of the center jets. Only a linear factor in
the largest address remains after differentiating the constant positions. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows
open scoped ContDiff

theorem schedule_coefficient_bounds {S S' B : ℝ} (hS : 0 ≤ S) (hSS : S ≤ S')
    (_hB : 0 ≤ B) (k target : ℕ) (hk : (k : ℝ) ≤ B) (ht : (target : ℝ) ≤ B)
    (terminal : Bool) :
    |S' * target - S * k| ≤ 4 * S' * (B + 2) ∧
    (|-((k : ℝ) + 1) * S| + |((k : ℝ) + 2) * S +
      (if terminal then S' else -S')|) ≤ 4 * S' * (B + 2) := by
  have hSp : 0 ≤ S' := hS.trans hSS
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ht0 : (0 : ℝ) ≤ target := Nat.cast_nonneg target
  constructor
  · apply (abs_sub _ _).trans
    rw [abs_of_nonneg (mul_nonneg hSp ht0), abs_of_nonneg (mul_nonneg hS hk0)]
    have h₁ := mul_le_mul_of_nonneg_left ht hSp
    have h₂ := mul_le_mul hSS hk hk0 hSp
    nlinarith
  · have he : |(if terminal then S' else -S')| = S' := by
      cases terminal <;> simp [abs_of_nonneg hSp]
    have h₁ : |-((k : ℝ) + 1) * S| = ((k : ℝ) + 1) * S := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg hS]
    have h₂ := abs_add_le (((k : ℝ)+2)*S) (if terminal then S' else -S')
    rw [he, abs_of_nonneg (by positivity : 0 ≤ ((k : ℝ)+2)*S)] at h₂
    rw [h₁]
    have h₃ := mul_le_mul hSS (by linarith : (k : ℝ)+1 ≤ B+1)
      (by positivity : 0 ≤ (k : ℝ)+1) hSp
    have h₄ := mul_le_mul hSS (by linarith : (k : ℝ)+2 ≤ B+2)
      (by positivity : 0 ≤ (k : ℝ)+2) hSp
    nlinarith

theorem scheduledCenter_coordinate_jet_bound {C B S S' T : ℝ} {m n : ℕ}
    (hC0 : 0 ≤ C)
    (hC : ∀ i ≤ m, ∀ t, |iteratedDeriv i (smoothRamp 0 1) t| ≤ C)
    (hS : 0 ≤ S) (hSS : S ≤ S') (hB : 0 ≤ B) (hT : 1 ≤ T)
    (hn : 1 ≤ n) (hnm : n ≤ m) (a : ℝ) (k target : ℕ)
    (hk : (k : ℝ) ≤ B) (ht : (target : ℝ) ≤ B)
    (terminal : Bool) (j : Fin 2) (t : ℝ) :
    |iteratedDeriv n (fun s => scheduledCenter a T S S' k target terminal s j) t| ≤
      (4 * S' * (B + 2)) * ((6 : ℝ)^m / T * C) := by
  have hs := schedule_coefficient_bounds hS hSS hB k target hk ht terminal
  have hscale : |(T/6)⁻¹|^n * C ≤ (6 : ℝ)^m / T * C :=
    mul_le_mul_of_nonneg_right (clock_inverse_power_bound hT hn hnm) hC0
  have hcoeff : 0 ≤ 4*S'*(B+2) := by have := hS.trans hSS; positivity
  fin_cases j
  · exact (scheduledCenter_horizontal_jet hC (by omega) hnm a T S S' t k target terminal).trans
      (mul_le_mul hs.1 hscale (by positivity) hcoeff)
  · exact (scheduledCenter_vertical_jet hC (by omega) hnm a T S S' t k target terminal).trans
      (mul_le_mul hs.2 hscale (by positivity) hcoeff)

end ForcedComputation.ExpandingDetector

end

end OAI
