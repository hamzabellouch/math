import OAI.Geometry.IsometricImmersion.Flows.FlowLowBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_seed_gap {M s0 s1 t : ℝ} (hM : 0 ≤ M)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hs0 : s0 ∈ Ioo (-2 : ℝ) 2) (hs1 : s1 ∈ Ioo (-2 : ℝ) 2)
    (ht : t ∈ Ioo (-2 : ℝ) 2) (hss : s0 ≤ s1) :
    Real.exp (-2 * M) * (s1 - s0) ≤ Y s1 t - Y s0 t := by
  have hd (s : ℝ) (hs : s ∈ Ioo (-2 : ℝ) 2) :
      DifferentiableAt ℝ (fun r => Y r t) s :=
    (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).differentiableAt
  have hc : ContinuousOn (fun r => Y r t) (Ioo (-2 : ℝ) 2) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hdi : DifferentiableOn ℝ (fun r => Y r t) (interior (Ioo (-2 : ℝ) 2)) := by
    intro s hs
    exact (hd s (interior_subset hs)).differentiableWithinAt
  have hbound : ∀ s ∈ interior (Ioo (-2 : ℝ) 2),
      Real.exp (-2 * M) ≤ deriv (fun r => Y r t) s := by
    intro s hs
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hq1
      (interior_subset hs) ht).1
  exact (convex_Ioo (-2 : ℝ) 2).mul_sub_le_image_sub_of_le_deriv hc hdi hbound
    s0 hs0 s1 hs1 hss

theorem cap_flow_time_lipschitz
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    {s t0 t1 : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2)
    (ht0 : t0 ∈ Ioo (-2 : ℝ) 2) (ht1 : t1 ∈ Ioo (-2 : ℝ) 2) :
    |Y s t1 - Y s t0| ≤ ((1 : ℝ) / 100) * |t1 - t0| := by
  have hd (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) : DifferentiableAt ℝ (Y s) t :=
    (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).differentiableAt
  have hb (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) : ‖deriv (Y s) t‖ ≤ (1 : ℝ) / 100 := by
    simpa only [Real.norm_eq_abs, timeFlowDerivative] using
      cap_flow_time_bound hq hU hSU hY hrange hstart hode hq0 hs ht
  simpa only [Real.norm_eq_abs] using
    (convex_Ioo (-2 : ℝ) 2).norm_image_sub_le_of_norm_deriv_le hd hb ht0 ht1

end SmoothLocal.Flow

end

end OAI
