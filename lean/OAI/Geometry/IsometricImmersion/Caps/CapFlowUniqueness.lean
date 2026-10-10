import OAI.Geometry.IsometricImmersion.Flows.FlowTransport
import OAI.Geometry.IsometricImmersion.Metrics.MetricLocality
import Mathlib.Analysis.ODE.ExistUnique

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem cap_trajectory_mem_ball_of_displacement {Y : ℝ → ℝ → ℝ}
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    {s t : ℝ} (hs : s ∈ Ioo (-2:ℝ) 2) (ht : t ∈ Ioo (-2:ℝ) 2) :
    Y s t ∈ closedBall (0:ℝ) 3 := by
  have hp : coordinatePoint t s ∈ capChartDomain := by
    change coordinatePoint t s 0 ∈ Ioo (-2:ℝ) 2 ∧ coordinatePoint t s 1 ∈ Ioo (-2:ℝ) 2
    simpa [coordinatePoint] using (show t ∈ Ioo (-2:ℝ) 2 ∧ s ∈ Ioo (-2:ℝ) 2 from ⟨ht,hs⟩)
  have hd : |Y s t-s| ≤ (1:ℝ)/50 := by
    simpa [capFlowHeight,coordinatePoint] using hdisp (coordinatePoint t s) hp
  have hy : |Y s t| ≤ 3 := by
    have hh : |Y s t| ≤ |Y s t-s|+|s| := by
      simpa only [sub_add_cancel] using abs_add_le (Y s t-s) s
    have hs' : |s| < 2 := abs_lt.mpr hs
    linarith
  simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hy

theorem capChart_eqOn_of_same_ode
    {q : Coord → ℝ} {U : Set Coord} {Y Z : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hYstart : ∀ s ∈ Icc (-2:ℝ) 2, Y s 0 = s)
    (hYode : ∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2:ℝ) 2) t)
    (hYdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    (hZstart : ∀ s ∈ Icc (-2:ℝ) 2, Z s 0 = s)
    (hZode : ∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
      HasDerivWithinAt (Z s) (-q (coordinatePoint t (Z s t))) (Icc (-2:ℝ) 2) t)
    (hZdisp : ∀ p ∈ capChartDomain, |capFlowHeight Z p-p 1| ≤ (1:ℝ)/50) :
    EqOn (capChart Y) (capChart Z) capChartDomain := by
  obtain ⟨K,hK⟩ := exists_flowField_lipschitz hq hU hSU
  have hsame (s : ℝ) (hs : s ∈ Ioo (-2:ℝ) 2) : EqOn (Y s) (Z s) (Ioo (-2:ℝ) 2) := by
    have hs' : s ∈ Icc (-2:ℝ) 2 := ⟨hs.1.le,hs.2.le⟩
    apply ODE_solution_unique_of_mem_Ioo
      (v := flowField q) (s := fun _ => closedBall (0:ℝ) 3)
      (fun t ht => hK t ⟨ht.1.le,ht.2.le⟩) (t₀ := 0) (by norm_num)
    · intro t ht
      exact ⟨(hYode s hs' t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2),
        cap_trajectory_mem_ball_of_displacement hYdisp hs ht⟩
    · intro t ht
      exact ⟨(hZode s hs' t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2),
        cap_trajectory_mem_ball_of_displacement hZdisp hs ht⟩
    · rw [hYstart s hs',hZstart s hs']
  intro p hp
  unfold capChart capFlowHeight
  rw [hsame (p 1) hp.2 hp.1]

theorem capPullback_eventuallyEq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) {p : Coord} (hp : p ∈ capChartDomain) :
    capPullback Y f =ᶠ[𝓝 p] capPullback Z f := by
  filter_upwards [capChartDomain_isOpen.mem_nhds hp] with r hr
  exact congrArg f (heq hr)

theorem capPullback_all_jets_eq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) (dirs : List (Fin 2)) {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial dirs (capPullback Y f) p = iteratedCoordPartial dirs (capPullback Z f) p :=
  (iteratedCoordPartial_eventuallyEq (capPullback_eventuallyEq_of_chart_eqOn heq f hp) dirs).self_of_nhds

theorem capChart_images_eq_of_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    {S : Set Coord} (hS : S ⊆ capChartDomain) : capChart Y '' S = capChart Z '' S :=
  Set.image_congr (fun _ hp => heq (hS hp))

theorem capPullback_square_rectangle_eq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) =
      rectangleIntegral tl tr sb st (fun p => (capPullback Z f p)^2) := by
  apply rectangleIntegral_congr ht hs
  intro p hp
  exact congrArg (fun x : Coord => (f x)^2) (heq (hbox hp))

theorem capPullback_gradient_rectangle_eq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    rectangleIntegral tl tr sb st (fun p => (coordPartial 0 (capPullback Y f) p)^2+
        (coordPartial 1 (capPullback Y f) p)^2) =
      rectangleIntegral tl tr sb st (fun p => (coordPartial 0 (capPullback Z f) p)^2+
        (coordPartial 1 (capPullback Z f) p)^2) := by
  apply rectangleIntegral_congr ht hs
  intro p hp
  change (coordPartial 0 (capPullback Y f) p)^2 + (coordPartial 1 (capPullback Y f) p)^2 =
    (coordPartial 0 (capPullback Z f) p)^2 + (coordPartial 1 (capPullback Z f) p)^2
  rw [coordPartial_eq_of_eventuallyEq (capPullback_eventuallyEq_of_chart_eqOn heq f (hbox hp)) 0,
    coordPartial_eq_of_eventuallyEq (capPullback_eventuallyEq_of_chart_eqOn heq f (hbox hp)) 1]

end SmoothLocal.Flow

end

end OAI
