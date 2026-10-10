import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace OAI

/-! # Ball transport by pairwise metric control on a full-measure support -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

omit [BorelSpace X] in
theorem map_ball_bound_of_pair_control (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (S : Set X) (hS : ∀ᵐ x ∂μ, x ∈ S) {r R : ℝ} {C : ℝ≥0∞}
    (hpair : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) < 2*r → dist x y < R)
    (hball : ∀ x, μ (ball x R) ≤ C) (a : Y) :
    (Measure.map f μ) (ball a r) ≤ C := by
  rw [Measure.map_apply hf measurableSet_ball]
  by_cases he : (S ∩ f ⁻¹' ball a r).Nonempty
  · obtain ⟨x,hxS,hxa⟩ := he
    apply (measure_mono_ae ?_).trans (hball x)
    filter_upwards [hS] with y hy hya
    exact hpair y hy x hxS ((dist_triangle (f y) a (f x)).trans_lt
      (by linarith [show dist (f y) a < r from hya,show dist (f x) a < r from hxa,
        dist_comm a (f x)]))
  · have hz : μ (f ⁻¹' ball a r) = 0 := by
      apply measure_mono_null (t := Sᶜ)
      · intro x hx hxS
        exact he ⟨x,hxS,hx⟩
      · exact ae_iff.mp hS
    rw [hz]
    exact zero_le

end Falconer

end OAI
