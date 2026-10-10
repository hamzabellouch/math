import OAI.Geometry.IsometricImmersion.Flows.FlowChart
import OAI.Geometry.IsometricImmersion.Flows.FlowTransport
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Determinant

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capChart_injOn_of_pairChart
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y) :
    InjOn (capChart Y) capChartDomain := by
  intro p hp r hr hsame
  have hp' : (p 0,p 1) ∈ e.source := by rw [hsource]; exact hp
  have hr' : (r 0,r 1) ∈ e.source := by rw [hsource]; exact hr
  have hpair : e (p 0,p 1) = e (r 0,r 1) := by
    rw [heq]
    apply Prod.ext
    · simpa only [triangularFlow,capChart_zero] using congrArg (fun q : Coord => q 0) hsame
    · simpa only [triangularFlow,capChart_one,capFlowHeight] using congrArg (fun q : Coord => q 1) hsame
  have hinj := e.injOn hp' hr' hpair
  ext i
  fin_cases i
  · exact congrArg Prod.fst hinj
  · exact congrArg Prod.snd hinj

theorem capChart_fderiv_matrix {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    {p : Coord} (hp : p ∈ capChartDomain) :
    LinearMap.toMatrix' (fderiv ℝ (capChart Y) p).toLinearMap =
      !![1,0; coordPartial 0 (capFlowHeight Y) p,coordPartial 1 (capFlowHeight Y) p] := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change coordPartial j (capChart Y) p i = _
  rw [capChart_partial hYs hp j]
  fin_cases i <;> fin_cases j <;> simp

theorem capChart_det_fderiv {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    {p : Coord} (hp : p ∈ capChartDomain) :
    (fderiv ℝ (capChart Y) p).det = coordPartial 1 (capFlowHeight Y) p := by
  rw [ContinuousLinearMap.det,←LinearMap.det_toMatrix',capChart_fderiv_matrix hYs hp]
  simp [Matrix.det_fin_two]

theorem capChart_abs_det_fderiv {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |(fderiv ℝ (capChart Y) p).det| = coordPartial 1 (capFlowHeight Y) p := by
  rw [capChart_det_fderiv hYs hp,abs_of_pos (capFlowHeight_partial_initial_pos hYs hvar hp)]

theorem capChart_jacobian_bounds
    {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) :
    Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
      coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M) := by
  have hYs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  rw [←(capFlowHeight_hasDerivAt_initial hYs hp).deriv]
  exact cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hp.2 hp.1

end SmoothLocal.Flow

end

end OAI
