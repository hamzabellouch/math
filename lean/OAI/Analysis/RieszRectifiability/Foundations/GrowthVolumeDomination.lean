import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.PlanarPullbackMeasure
import OAI.Analysis.RieszRectifiability.Foundations.ClosedBallMeasureComparison

namespace OAI

/-!
# Volume domination from intrinsic upper growth

An upper growth bound in the intrinsic Euclidean dimension implies domination
by Lebesgue measure. The density bound is normalized by the unit-ball volume
and includes the dimensional factor needed for closed-ball comparison.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def intrinsicGrowthDensityBound (n : ℕ) (C : ℝ) : ℝ≥0 :=
  Real.toNNReal (C * 2 ^ n / (volume : Measure (Ambient n)).real (ball 0 1))

theorem intrinsic_growth_le_volume (n : ℕ) (C : ℝ) (μ : Measure (Ambient n))
    (hg : GlobalUpperGrowth n C μ) :
    μ ≤ intrinsicGrowthDensityBound n C • (volume : Measure (Ambient n)) := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts C μ hg
  let V : ℝ := (volume : Measure (Ambient n)).real (ball 0 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (ne_of_gt (measure_ball_pos volume (0 : Ambient n) zero_lt_one)) measure_ball_lt_top.ne
  have hD : (intrinsicGrowthDensityBound n C : ℝ) = C * 2 ^ n / V := by
    exact Real.coe_toNNReal _ (div_nonneg (mul_nonneg hg.1 (by positivity)) hV.le)
  have hDV : (intrinsicGrowthDensityBound n C : ℝ) * V = C * 2 ^ n := by
    rw [hD]
    exact div_mul_cancel₀ _ hV.ne'
  apply measure_le_of_closedBall_le
  intro x r hr
  have hvol : (volume : Measure (Ambient n)).real (closedBall x r) = r ^ n * V := by
    simpa only [Ambient, finrank_euclideanSpace, Fintype.card_fin] using!
      (Measure.addHaar_real_closedBall (volume : Measure (Ambient n)) x hr.le)
  have hid : (intrinsicGrowthDensityBound n C : ℝ) *
      (volume : Measure (Ambient n)).real (closedBall x r) = C * (2 * r) ^ n := by
    rw [hvol]
    calc
      _ = ((intrinsicGrowthDensityBound n C : ℝ) * V) * r ^ n := by ring
      _ = _ := by rw [hDV, mul_pow, mul_assoc]
  calc
    μ (closedBall x r) ≤ μ (ball x (2 * r)) :=
      measure_mono (closedBall_subset_ball (by linarith))
    _ ≤ ENNReal.ofReal (C * (2 * r) ^ n) := hg.2 x (2 * r) (by positivity)
    _ = ENNReal.ofReal ((intrinsicGrowthDensityBound n C : ℝ) *
        (volume : Measure (Ambient n)).real (closedBall x r)) := congrArg ENNReal.ofReal hid.symm
    _ = (intrinsicGrowthDensityBound n C • (volume : Measure (Ambient n)))
        (closedBall x r) := by
      rw [ENNReal.ofReal_mul (intrinsicGrowthDensityBound n C).coe_nonneg,
        ENNReal.ofReal_coe_nnreal, Measure.real,
        ENNReal.ofReal_toReal (measure_closedBall_lt_top.ne), Measure.coe_nnreal_smul_apply]

theorem intrinsic_growth_absolutelyContinuous (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient n)) (hg : GlobalUpperGrowth n C μ) :
    μ ≪ (volume : Measure (Ambient n)) :=
  (intrinsic_growth_le_volume n C μ hg).absolutelyContinuous.trans
    Measure.smul_absolutelyContinuous

end

end RieszRectifiability

end OAI
