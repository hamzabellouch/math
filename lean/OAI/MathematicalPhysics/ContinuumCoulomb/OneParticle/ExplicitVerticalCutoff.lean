import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.BumpFunction.Basic

namespace OAI

/-! An explicit smooth transverse cutoff. Its formula uses only the fixed
smooth transition function, so rational approximation can use the actual
exponential formula instead of a classically selected bump function. -/

noncomputable section
namespace ContinuumCoulomb

def verticalCutoffBump (z : ℝ) : ℝ :=
  Real.smoothTransition ((4-z^2)/3)

namespace verticalCutoffBump

theorem contDiff {n : ℕ∞} : ContDiff ℝ n verticalCutoffBump :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_id.pow 2)).div_const 3)

theorem nonneg {z : ℝ} : 0 ≤ verticalCutoffBump z :=
  Real.smoothTransition.nonneg _

theorem le_one {z : ℝ} : verticalCutoffBump z ≤ 1 :=
  Real.smoothTransition.le_one _

theorem one_of_mem_closedBall {z : ℝ} (hz : z ∈ Metric.closedBall (0 : ℝ) 1) :
    verticalCutoffBump z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hab : |z| ≤ 1 := by simpa [Metric.mem_closedBall, Real.dist_eq] using hz
  have hsq := (sq_le_sq₀ (abs_nonneg z) (by norm_num : (0:ℝ) ≤ 1)).mpr hab
  rw [sq_abs] at hsq
  linarith

theorem zero_of_le_dist {z : ℝ} (hz : 2 ≤ dist z 0) :
    verticalCutoffBump z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hab : 2 ≤ |z| := by simpa [Real.dist_eq] using hz
  have hsq := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg z)).mpr hab
  rw [sq_abs] at hsq
  linarith

theorem hasCompactSupport : HasCompactSupport verticalCutoffBump := by
  apply (isCompact_closedBall (0 : ℝ) 2).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  by_contra hn
  have hd : 2 ≤ dist z 0 := (lt_of_not_ge (by simpa [Metric.mem_closedBall] using hn)).le
  exact hz (zero_of_le_dist hd)

end verticalCutoffBump
end ContinuumCoulomb

end

end OAI
