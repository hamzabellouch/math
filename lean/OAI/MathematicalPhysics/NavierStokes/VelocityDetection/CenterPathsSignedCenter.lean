import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CenterPaths
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.CenterPaths
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

def signedCenter (a T S S' σ₀ σ₁ : ℝ) (k l : ℕ) (t : ℝ) : Coord 2 :=
  center a T S S' σ₁ k l t + ![0, (1 - theta a T 0 t) * (σ₀ + 1) * S]

@[fun_prop] theorem contDiff_signedCenter (a T S S' σ₀ σ₁ : ℝ) (k l : ℕ) :
    ContDiff ℝ ∞ (signedCenter a T S S' σ₀ σ₁ k l) := by
  unfold signedCenter
  apply ContDiff.add (contDiff_center _ _ _ _ _ _ _)
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop

theorem signed_source_negative (a T S S' σ₁ : ℝ) (k l : ℕ) :
    signedCenter a T S S' (-1) σ₁ k l = center a T S S' σ₁ k l := by
  ext t i
  fin_cases i <;> simp [signedCenter]

theorem signed_start (a T S S' σ₀ σ₁ : ℝ) (k l : ℕ) :
    signedCenter a T S S' σ₀ σ₁ k l a = ![S * k, σ₀ * S] := by
  rw [signedCenter, center_start]
  have ht : theta a T 0 a = 0 := by
    simp only [theta, sub_self, mul_zero, zero_div, Nat.cast_zero]
    exact ramp_zero (by norm_num)
  rw [ht]
  ext i
  fin_cases i <;> simp
  ring

theorem signed_end {T : ℝ} (hT : 0 < T) (a S S' σ₀ σ₁ : ℝ) (k l : ℕ) :
    signedCenter a T S S' σ₀ σ₁ k l (a + T) = ![S' * l, σ₁ * S'] := by
  rw [signedCenter, center_end hT]
  have ht : theta a T 0 (a + T) = 1 := by
    simp only [theta, add_sub_cancel_left, Nat.cast_zero, sub_zero]
    rw [mul_div_cancel_right₀ _ hT.ne']
    exact ramp_one (by norm_num)
  rw [ht]
  ext i
  fin_cases i <;> simp

end VelocityDetection.CenterPaths
end

end OAI
