import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # The actual second positive-time derivative of the heat semigroup

Only the second generator iterate is needed for the heat-bridge variation.
The fixed positive-time splitting avoids differentiating an unbounded operator.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

def heatSecondGeneratorAt (t : ℝ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  heatGeneratorAt μ Q (t/2) (heatGeneratorAt μ Q (t/2) f)

theorem heatGeneratorAt_hasDerivAt_second (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => heatGeneratorAt μ Q s f) (-heatSecondGeneratorAt μ Q t f) t := by
  have hhalf : t-t/2=t/2 := by ring
  simpa only [heatSecondGeneratorAt,hhalf] using
    heatGeneratorAt_hasDerivAt_split μ Q f (half_pos ht) (by linarith : t/2<t)

theorem heatAt_deriv_hasDerivAt (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (fun s => heatAt μ Q s f)) (heatSecondGeneratorAt μ Q t f) t := by
  have hd := (heatGeneratorAt_hasDerivAt_second μ Q f ht).neg
  simp only [neg_neg] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact (heatAt_hasDerivAt μ Q s hs f).deriv

end RegularPointCoordinates

end

end OAI
