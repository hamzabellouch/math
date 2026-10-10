import OAI.Geometry.RCD.Metric.MonotoneSpatialMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Measurable gluing of compatible local heat-potential limits

The gluing uses a single countable exceptional time set. No agreement or
temporal continuity at exceptional times is asserted.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem glue_heat_cylinder_limits {X : Type*} [MetricSpace X] [SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (z : X) (r δ : ℕ → ℝ)
    (N : Set ℝ) (hN : N.Countable)
    (g : ∀ m, ℝ → closedBall z (r m) → ℝ)
    (hc : ∀ m t, Continuous (g m t))
    (hm : ∀ m x, Monotone (fun t => g m t x))
    (heq : ∀ i j t, t ∈ Ioo (δ i) 1 → t ∈ Ioo (δ j) 1 → t ∉ N →
      ∀ x (hi : x ∈ closedBall z (r i)) (hj : x ∈ closedBall z (r j)),
        g i t ⟨x,hi⟩ = g j t ⟨x,hj⟩) :
    ∃ G : ℝ → X → ℝ, Measurable (Function.uncurry G) ∧
      ∀ m t, t ∈ Ioo (δ m) 1 → t ∉ N → ∀ x (hx : x ∈ closedBall z (r m)),
        G t x = g m t ⟨x,hx⟩ := by
  classical
  let A := fun m => {q : ℝ × X | q.2 ∈ closedBall z (r m)}
  have hA (m : ℕ) : MeasurableSet (A m) := measurable_snd measurableSet_closedBall
  let E := fun m (q : ℝ × X) =>
    if hx : q.2 ∈ closedBall z (r m) then g m q.1 ⟨q.2,hx⟩ else 0
  have hE (m : ℕ) : Measurable (E m) := by
    have hg : Measurable (Function.uncurry (g m)) :=
      monotone_spatial_measurable (g m) (hc m) (hm m)
    have hi : Measurable (fun q : A m => (q.val.1,(⟨q.val.2,q.property⟩ : closedBall z (r m)))) :=
      (measurable_fst.comp measurable_subtype_coe).prodMk
        ((measurable_snd.comp measurable_subtype_coe).subtype_mk)
    have hh : Measurable (fun q : A m => g m q.val.1 ⟨q.val.2,q.property⟩) := hg.comp hi
    exact hh.dite measurable_const (hA m)
  let U := fun m => (Ioo (δ m) 1 \ N) ×ˢ closedBall z (r m)
  have hU (m : ℕ) : MeasurableSet (U m) :=
    (measurableSet_Ioo.diff hN.measurableSet).prod measurableSet_closedBall
  have hcompat : Pairwise (fun i j => EqOn (E i) (E j) (U i ∩ U j)) := by
    intro i j _ q hq
    have hi : q.2 ∈ closedBall z (r i) := hq.1.2
    have hj : q.2 ∈ closedBall z (r j) := hq.2.2
    dsimp only [E]
    rw [dite_eq_left hi,dite_eq_left hj]
    exact heq i j q.1 hq.1.1.1 hq.2.1.1 hq.1.1.2 q.2 hi hj
  obtain ⟨G,hG,hGE⟩ := exists_measurable_piecewise U hU E hE hcompat
  refine ⟨fun t x => G (t,x),hG,?_⟩
  intro m t ht htN x hx
  have hh := hGE m (show (t,x) ∈ U m from ⟨⟨ht,htN⟩,hx⟩)
  simpa only [E,dite_eq_left hx] using hh

end RegularPointCoordinates

end

end OAI
