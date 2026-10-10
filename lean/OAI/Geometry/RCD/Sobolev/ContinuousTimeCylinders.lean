import OAI.Geometry.RCD.Sobolev.GoodTimeExtension
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OAI

/-! # Continuity and measurability from local Lipschitz time cylinders -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem goodTimeExtension_regular {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (z : X) (N : Set ℝ) (G : ℝ → X → ℝ)
    (hlocal : ∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 < δ →
      ∃ L : ℝ≥0, LipschitzOnWith L (Function.uncurry (goodTimeExtension N G))
        (Ioo δ 1 ×ˢ closedBall z r)) :
    ContinuousOn (Function.uncurry (goodTimeExtension N G)) (Ioo 0 1 ×ˢ univ) ∧
      Measurable (Function.uncurry (goodTimeExtension N G)) := by
  have hc : ContinuousOn (Function.uncurry (goodTimeExtension N G)) (Ioo 0 1 ×ˢ univ) := by
    intro q hq
    let r := dist q.2 z+1
    have hr : 0 < r := by dsimp only [r]; positivity
    have hδ : 0 < q.1/2 := half_pos hq.1.1
    obtain ⟨L,hL⟩ := hlocal r hr (q.1/2) hδ
    have ht : q.1 ∈ Ioo (q.1/2) 1 := ⟨by linarith [hq.1.1],hq.1.2⟩
    have hx : q.2 ∈ ball z r := by simp only [mem_ball,r]; linarith
    have hn : Ioo (q.1/2) 1 ×ˢ closedBall z r ∈ 𝓝 q :=
      prod_mem_nhds (isOpen_Ioo.mem_nhds ht) (closedBall_mem_nhds_of_mem hx)
    exact ((hL.continuousOn q ⟨ht,ball_subset_closedBall hx⟩).continuousAt hn).continuousWithinAt
  refine ⟨hc,?_⟩
  classical
  have hm := hc.measurable_piecewise (g := fun _ => (0:ℝ)) continuousOn_const
    (measurableSet_Ioo.prod MeasurableSet.univ)
  have he : (Ioo (0:ℝ) 1 ×ˢ (univ : Set X)).piecewise
      (Function.uncurry (goodTimeExtension N G)) (fun _ => 0) =
      Function.uncurry (goodTimeExtension N G) := by
    funext q
    by_cases hq : q.1 ∈ Ioo (0:ℝ) 1
    · simp only [Set.piecewise,mem_prod,mem_univ,and_true,hq,ite_eq_left]
    · simp only [Set.piecewise,mem_prod,mem_univ,and_true,hq,
        Function.uncurry,goodTimeExtension,ite_false]
  rwa [he] at hm

end RegularPointCoordinates

end

end OAI
