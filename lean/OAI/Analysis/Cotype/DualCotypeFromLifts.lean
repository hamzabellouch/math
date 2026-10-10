import OAI.Analysis.Cotype.FiniteL2DualNorm

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem fixedCotypeBound_dual_of_L2_lifts {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z : Fin m → X, ∃ H : Cube m → X,
      (∀ i, moment X H i = z i) ∧ cubeL2 X H ≤ C * Real.sqrt (∑ i, ‖z i‖^2)) :
    FixedCotypeBound (X →L[ℝ] ℝ) m C := by
  refine ⟨hC, fun θ => ?_⟩
  have hb : ‖finiteL2Dual θ‖ ≤ C * cubeL2 (X →L[ℝ] ℝ) (rademacherSum (X →L[ℝ] ℝ) θ) := by
    apply (finiteL2Dual θ).opNorm_le_bound (mul_nonneg hC (cubeL2_nonneg _))
    intro z
    obtain ⟨H,hm,hn⟩ := h (fun i => z i)
    have he : finiteL2Dual θ z = dualPairing H (rademacherSum (X →L[ℝ] ℝ) θ) := by
      simp only [finiteL2Dual_apply, ← hm, dualPairing, rademacherSum, moment,
        average, map_smul, map_sum, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [he, Real.norm_eq_abs]
    have hn' : cubeL2 X H ≤ C * ‖z‖ := by simpa only [PiLp.norm_eq_of_L2] using hn
    calc
      _ ≤ cubeL2 X H * cubeL2 (X →L[ℝ] ℝ) (rademacherSum (X →L[ℝ] ℝ) θ) := dualPairing_bound _ _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hn' (cubeL2_nonneg (rademacherSum (X →L[ℝ] ℝ) θ))]
  simpa only [finiteL2Dual_norm, PiLp.norm_eq_of_L2, ofLp_toLp] using hb

end Cotype

end

end OAI
