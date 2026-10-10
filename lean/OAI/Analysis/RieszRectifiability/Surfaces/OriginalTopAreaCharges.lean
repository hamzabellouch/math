import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelOriginalMass
import OAI.Analysis.RieszRectifiability.Nets.SupportCellRoot

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def enlargedTopMassConstant (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (G * 4 ^ n) * ENNReal.ofReal (C * 8 ^ n)

theorem enlargedTopMassConstant_lt_top (n : ℕ) (C G : ℝ) :
    enlargedTopMassConstant n C G < ⊤ := by
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem clean_top_radius_power_le_mass {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    (ENNReal.ofReal (latticeRadius R k)) ^ n ≤
      ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z) := by
  simpa only [SupportCellDescendant.radius, SupportCellDescendant.cell, supportCellRoot, Nat.add_zero]
    using! SupportCellDescendant.radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z
      (supportCellRoot μ R hR k z)

theorem enlarged_top_ball_mass_le_clean_top {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    μ (closedBall (z : Ambient d) (3 * latticeRadius R k)) ≤
      enlargedTopMassConstant n C G * μ (cleanSupportCell μ R hR k z) := by
  have hr := latticeRadius_pos R hR k
  have hupper : μ (closedBall (z : Ambient d) (3 * latticeRadius R k)) ≤
      ENNReal.ofReal (G * 4 ^ n) * (ENNReal.ofReal (latticeRadius R k)) ^ n := by
    calc
      _ ≤ μ (ball (z : Ambient d) (4 * latticeRadius R k)) :=
        measure_mono (closedBall_subset_ball (by linarith))
      _ ≤ ENNReal.ofReal (G * (4 * latticeRadius R k) ^ n) :=
        hg.2 (z : Ambient d) (4 * latticeRadius R k) (by positivity)
      _ = _ := by
        rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul (by positivity : 0 ≤ G * 4 ^ n),
          ENNReal.ofReal_pow hr.le]
  have hlowerTop := clean_top_radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z
  calc
    _ ≤ ENNReal.ofReal (G * 4 ^ n) * (ENNReal.ofReal (latticeRadius R k)) ^ n := hupper
    _ ≤ ENNReal.ofReal (G * 4 ^ n) *
        (ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z)) := mul_le_mul_right hlowerTop _
    _ = _ := by unfold enlargedTopMassConstant; rw [mul_assoc]

end

end RieszRectifiability

end OAI
