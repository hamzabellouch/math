import OAI.Analysis.Cotype.ProjectionGenerator
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem complexProjectionTime_spectral {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (t : ℂ) :
    complexProjectionTime P t =
      ∑ ε : Cube m, Complex.exp (-(t * (projectionDegree ε : ℂ))) •
        complexDualLift (projectionPattern P ε) := by
  rw [complexProjectionTime, complexProjectionPolynomial_spectral]
  unfold complexSpectralEval
  apply Finset.sum_congr rfl
  intro ε _
  dsimp only
  rw [← Complex.exp_nat_mul]
  congr 2
  ring

theorem exists_vertical_time_for_circle {T : ℝ} (z : ℂ)
    (hz : ‖z‖ = Real.exp (-T)) :
    ∃ τ : ℝ, |τ| ≤ Real.pi ∧
      Complex.exp (-((T : ℂ) + (τ : ℂ)*Complex.I)) = z := by
  have hzne : z ≠ 0 := by
    intro h
    have := Real.exp_pos (-T)
    simp [h] at hz
    linarith
  refine ⟨-z.arg, by simpa using Complex.abs_arg_le_pi z, ?_⟩
  have he : (T : ℂ) + ((-z.arg : ℝ) : ℂ)*Complex.I = -Complex.log z := by
    apply Complex.ext
    · simp [Complex.log_re, hz, Real.log_exp]
    · simp [Complex.log_im]
  rw [he, neg_neg, Complex.exp_log hzne]

theorem projectionLinearCoefficient_bound_of_vertical_time
    {T B : ℝ} {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (P j))
    (hvertical : ∀ τ : ℝ, |τ| ≤ Real.pi →
      ‖complexProjectionTime P ((T : ℂ) + (τ : ℂ)*Complex.I)‖ ≤ B)
    (y : Y) :
    ‖projectionLinearCoefficient P y‖ ≤ (B / Real.exp (-T))*‖y‖ := by
  apply projectionLinearCoefficient_bound_of_complex_circle (Real.exp_pos (-T)) P hc
  intro z hz
  have hn : ‖z‖ = Real.exp (-T) := by simpa [Metric.mem_sphere, dist_zero_right] using hz
  obtain ⟨τ, hτ, he⟩ := exists_vertical_time_for_circle z hn
  have hb := hvertical τ hτ
  simpa only [complexProjectionTime, he] using hb

end Cotype

end

end OAI
