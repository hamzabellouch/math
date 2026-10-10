import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # The precise Sobolev norm growth of a radial cutoff -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem radialSobolevCutoff_norm_sq_le (p : X) {R : ℝ} (hR : 0 < R) :
    ‖radialSobolevCutoff μ Q p hR‖^2 ≤ (1+R⁻¹^2)*μ.real (closedBall p (2*R)) := by
  let ψ := radialSobolevCutoff μ Q p hR
  let S := closedBall p (2*R)
  have hS : MeasurableSet S := measurableSet_closedBall
  have hi : Integrable (S.indicator (fun _ : X => (1:ℝ))) μ :=
    (integrable_indicator_iff hS).mpr (integrableOn_const (isCompact_closedBall p (2*R)).measure_lt_top.ne)
  have hLp : ‖SobolevSpace.toLp μ Q ψ‖^2 ≤ μ.real S := by
    rw [← integral_sq_Lp]
    calc
      _ ≤ ∫ x, S.indicator (fun _ : X => (1:ℝ)) x ∂μ := by
        apply integral_mono_ae (Lp.memLp _).integrable_sq hi
        filter_upwards [radialSobolevCutoff_coe μ Q p hR] with x hx
        change SobolevSpace.toLp μ Q ψ x=radialCutoff p R x at hx
        rw [hx]
        by_cases hs : x∈S
        · rw [indicator_of_mem hs]
          nlinarith [(radialCutoff_bounds p R x).1,(radialCutoff_bounds p R x).2]
        · rw [indicator_of_notMem hs,radialCutoff_eq_zero p hR]
          · norm_num
          · exact (lt_of_not_ge (by simpa only [S,mem_closedBall,dist_comm] using hs)).le
      _ = _ := integral_indicator_one hS
  have hE := radialSobolevCutoff_energy_le μ Q p hR
  rw [SobolevSpace.norm_sq,SobolevSpace.normSq]
  calc
    _ ≤ μ.real S+2*(μ.real S/(2*R^2)) := add_le_add hLp (mul_le_mul_of_nonneg_left hE (by norm_num))
    _ = _ := by
      dsimp only [S]
      field_simp

theorem radialSobolevCutoff_norm_le (p : X) {R : ℝ} (hR : 0 < R) :
    ‖radialSobolevCutoff μ Q p hR‖ ≤ Real.sqrt ((1+R⁻¹^2)*μ.real (closedBall p (2*R))) := by
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (radialSobolevCutoff_norm_sq_le μ Q p hR)

end RegularPointCoordinates

end

end OAI
