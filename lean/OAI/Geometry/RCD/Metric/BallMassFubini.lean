import OAI.Geometry.RCD.Metric.ClosedBallMassLimit
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Integrating the masses of translated Euclidean balls -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem lintegral_closedBall_mass {n : ℕ}
    (μ : Measure (Euclidean n)) [IsFiniteMeasure μ] (r : ℝ) :
    (∫⁻ z, μ (closedBall z r)) = volume (closedBall (0 : Euclidean n) r)*μ univ := by
  classical
  let F : Euclidean n × Euclidean n → ℝ≥0∞ :=
    {q | dist q.2 q.1 ≤ r}.indicator (fun _ => 1)
  have hset : MeasurableSet {q : Euclidean n × Euclidean n | dist q.2 q.1 ≤ r} :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have hF : Measurable F := measurable_const.indicator hset
  have hleft (z : Euclidean n) : (fun x => F (z,x)) =
      (closedBall z r).indicator (fun _ => (1 : ℝ≥0∞)) := by rfl
  have hright (x : Euclidean n) : (fun z => F (z,x)) =
      (closedBall x r).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    simp only [F,Set.indicator_apply,mem_ofPred_eq,mem_closedBall,dist_comm]
  have hl (z : Euclidean n) : (∫⁻ x, F (z,x) ∂μ)=μ (closedBall z r) := by
    rw [hleft,lintegral_indicator_const measurableSet_closedBall,one_mul]
  have hr (x : Euclidean n) : (∫⁻ z, F (z,x))=volume (closedBall (0 : Euclidean n) r) := by
    rw [hright,lintegral_indicator_const measurableSet_closedBall,one_mul,
      Measure.addHaar_closedBall_center volume x r]
  calc
    _ = ∫⁻ z, ∫⁻ x, F (z,x) ∂μ := lintegral_congr (fun z => (hl z).symm)
    _ = ∫⁻ x, ∫⁻ z, F (z,x) ∂volume ∂μ :=
      lintegral_lintegral_swap (μ := volume) (ν := μ) (f := fun z x => F (z,x)) hF.aemeasurable
    _ = ∫⁻ _x, volume (closedBall (0 : Euclidean n) r) ∂μ := lintegral_congr hr
    _ = _ := lintegral_const _

end RegularPointCoordinates

end

end OAI
