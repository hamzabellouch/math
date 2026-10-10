import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalNeighborhood

namespace OAI

/-! Even moments of the vertical Sobolev majorant. The constants are
independent of the number of packet sums and of their Hilbert dimension. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem average_natPow_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] (f : Ω → ℝ) (n : ℕ)
    (hf : Integrable f μ) (hfn : Integrable (fun t => f t ^ n) μ)
    (hf0 : ∀ᵐ t ∂μ, 0 ≤ f t) :
    (⨍ t, f t ∂μ)^n ≤ ⨍ t, f t^n ∂μ := by
  exact (convexOn_pow n).map_average_le (continuous_id.pow n).continuousOn
    isClosed_Ici hf0 hf hfn

theorem averaged_square_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] (V D : Ω → ℝ) (n : ℕ)
    (hV : Integrable (fun t => V t^2) μ) (hD : Integrable (fun t => D t^2) μ)
    (hn : Integrable (fun t => (V t^2 + D t^2)^n) μ)
    (hVn : Integrable (fun t => V t^(2*n)) μ)
    (hDn : Integrable (fun t => D t^(2*n)) μ) :
    (2 * ⨍ t, V t^2 + D t^2 ∂μ)^n ≤
      4^n * ⨍ t, V t^(2*n) + D t^(2*n) ∂μ := by
  have hj := average_natPow_le μ (fun t => V t^2 + D t^2) n (hV.add hD) hn
    (Filter.Eventually.of_forall fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hp (t : Ω) : (V t^2 + D t^2)^n ≤
      2^n * (V t^(2*n) + D t^(2*n)) := by
    calc
      _ ≤ 2^(n-1) * ((V t^2)^n + (D t^2)^n) := add_pow_le (sq_nonneg _) (sq_nonneg _) n
      _ ≤ 2^n * ((V t^2)^n + (D t^2)^n) := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)) (by positivity)
      _ = _ := by simp only [pow_mul]
  have ha := integral_mono_ae hn ((hVn.add hDn).const_mul (2^n))
    (Filter.Eventually.of_forall hp)
  dsimp only [Pi.add_apply] at ha
  rw [integral_const_mul] at ha
  have hav : (⨍ t, (V t^2 + D t^2)^n ∂μ) ≤
      2^n * ⨍ t, V t^(2*n) + D t^(2*n) ∂μ := by
    simp only [average_eq, smul_eq_mul]
    calc
      _ ≤ (μ.real univ)⁻¹ * (2^n * ∫ t, V t^(2*n) + D t^(2*n) ∂μ) :=
        mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr measureReal_nonneg)
      _ = _ := by ring
  calc
    _ = 2^n * (⨍ t, V t^2 + D t^2 ∂μ)^n := mul_pow _ _ _
    _ ≤ 2^n * (2^n * ⨍ t, V t^(2*n) + D t^(2*n) ∂μ) := by
      exact mul_le_mul_of_nonneg_left (hj.trans hav) (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

end LipschitzHilbert

end

end OAI
