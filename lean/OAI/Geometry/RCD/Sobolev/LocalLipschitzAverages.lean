import OAI.Geometry.RCD.Heat.HeatPoissonAverage

namespace OAI

/-! # Ball averages controlled by a local Lipschitz representative -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsLocallyFiniteMeasure μ]

/-- Only Lipschitz control on the set containing the two averaging balls is
needed; a real-valued Lipschitz extension is used solely for this estimate. -/
theorem local_lipschitz_ball_average_bound {S : Set X} {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) (x y : X) {r : ℝ} (hr : 0 ≤ r)
    (hx : μ (closedBall x r) ≠ 0) (hy : μ (closedBall y r) ≠ 0)
    (hxS : closedBall x r ⊆ S) (hyS : closedBall y r ⊆ S) :
    |(⨍ z in closedBall x r, f z ∂μ)-(⨍ z in closedBall y r, f z ∂μ)| ≤
      L*(dist x y+2*r) := by
  obtain ⟨v,hv,he⟩ := hf.extend_real
  have hax : (⨍ z in closedBall x r, f z ∂μ) = ⨍ z in closedBall x r, v z ∂μ := by
    apply average_congr
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact he (hxS hz)
  have hay : (⨍ z in closedBall y r, f z ∂μ) = ⨍ z in closedBall y r, v z ∂μ := by
    apply average_congr
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact he (hyS hz)
  rw [hax,hay]
  have ha := average_lipschitz_center μ hv x hr hx
  have hb := average_lipschitz_center μ hv y hr hy
  have hd := hv.dist_le_mul x y
  rw [Real.dist_eq] at hd
  have htri := abs_add_three ((⨍z in closedBall x r,v z ∂μ)-v x) (v x-v y)
    (v y-(⨍z in closedBall y r,v z ∂μ))
  rw [abs_sub_comm (v y)] at htri
  have heq : ((⨍z in closedBall x r,v z ∂μ)-v x)+(v x-v y)+
      (v y-(⨍z in closedBall y r,v z ∂μ)) =
      (⨍z in closedBall x r,v z ∂μ)-(⨍z in closedBall y r,v z ∂μ) := by ring
  rw [heq] at htri
  nlinarith

end RegularPointCoordinates

end

end OAI
