import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDiffusionBudget
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingStageTimes

namespace OAI

/-! The fixed Laplacian constant is absorbed into the chosen spatial
scale. Every finite execution uses less than the fixed observation margin. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open scoped BigOperators

theorem concrete_stage_loss_le {ν C σ D K : ℝ}
    (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K) (hc : ν * C ≤ σ * 3000) (n : ℕ) :
    ν * ((radius σ D K n)⁻¹ ^ 2 * C) * duration σ D K n ≤
      σ * 3000 * (duration σ D K n / radius σ D K n ^ 2) := by
  have ht : 0 ≤ duration σ D K n := le_trans (by norm_num) (duration_ge_two hσ hD hK n)
  have hh := mul_le_mul_of_nonneg_right hc (div_nonneg ht (sq_nonneg (radius σ D K n)))
  convert hh using 1
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem finite_diffusion_loss_lt {ν C σ D K : ℝ}
    (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K) (hc : ν * C ≤ σ * 3000) (n : ℕ) :
    ν * ((radius σ D K 0)⁻¹ ^ 2 * C) * 2 +
      (∑ i ∈ Finset.range n, ν * ((radius σ D K i)⁻¹ ^ 2 * C) * duration σ D K i) < 1 / 24 := by
  have hinit : ν * ((radius σ D K 0)⁻¹ ^ 2 * C) * 2 ≤
      2 * σ * 3000 / initialRadius σ D K ^ 2 := by
    have hi := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ 2 / initialRadius σ D K ^ 2 by positivity)
    convert hi using 1 <;> simp [radius, div_eq_mul_inv, inv_pow] <;> ring
  have hsum : (∑ i ∈ Finset.range n, ν * ((radius σ D K i)⁻¹ ^ 2 * C) * duration σ D K i) ≤
      ∑' i, σ * 3000 * (duration σ D K i / radius σ D K i ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, σ * 3000 * (duration σ D K i / radius σ D K i ^ 2) :=
        Finset.sum_le_sum (fun i _ => concrete_stage_loss_le hσ hD hK hc i)
      _ ≤ _ := (diffusion_loss_summable hσ hD hK).sum_le_tsum _ (fun i _ => by
        apply mul_nonneg (by positivity)
        exact div_nonneg (le_trans (by norm_num) (duration_ge_two hσ hD hK i)) (sq_nonneg _))
  exact lt_of_le_of_lt (add_le_add hinit hsum) (total_two_time_diffusion_loss_lt hσ hD hK)

end ForcedComputation.ExpandingDetector

end

end OAI
