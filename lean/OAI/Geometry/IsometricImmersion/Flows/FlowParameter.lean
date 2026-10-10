import OAI.Geometry.IsometricImmersion.Caps.CapFlow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def verticalAverageDerivative (q : Coord → ℝ) (t y0 y1 : ℝ) : ℝ :=
  ∫ u in 0..1, coordPartial 1 q (coordinatePoint t (y0 + u * (y1 - y0)))

theorem verticalSegment_mem_modelSquare {t y0 y1 u : ℝ}
    (ht : t ∈ Icc (-2 : ℝ) 2) (hy0 : y0 ∈ Icc (-3 : ℝ) 3)
    (hy1 : y1 ∈ Icc (-3 : ℝ) 3) (hu : u ∈ Icc (0 : ℝ) 1) :
    coordinatePoint t (y0 + u * (y1 - y0)) ∈ modelSquare := by
  apply coordinatePoint_mem_modelSquare
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc := (convex_Icc (-3 : ℝ) 3) hy0 hy1
    (show 0 ≤ 1 - u by linarith [hu.2]) hu.1 (show (1 - u) + u = 1 by ring)
  have he : y0 + u * (y1 - y0) = (1 - u) * y0 + u * y1 := by ring
  rw [he]
  exact hc

theorem vertical_secant_identity {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {t y0 y1 : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2)
    (hy0 : y0 ∈ Icc (-3 : ℝ) 3) (hy1 : y1 ∈ Icc (-3 : ℝ) 3) :
    q (coordinatePoint t y1) - q (coordinatePoint t y0) =
      (y1 - y0) * verticalAverageDerivative q t y0 y1 := by
  let z (u : ℝ) := y0 + u * (y1 - y0)
  have hm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : coordinatePoint t (z u) ∈ U :=
    hSU (verticalSegment_mem_modelSquare ht hy0 hy1 hu)
  have hc : ContinuousOn (fun u => coordPartial 1 q (coordinatePoint t (z u)))
      (Icc (0 : ℝ) 1) :=
    (partial_contDiffOn hq hU 1).continuousOn.comp
      (by unfold coordinatePoint z; fun_prop) hm
  have hd (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v => q (coordinatePoint t (z v)))
        (coordPartial 1 q (coordinatePoint t (z u)) * (y1 - y0)) u := by
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    have hqy := ((hq.contDiffAt (hU.mem_nhds (hm u hu'))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt (z u) (coordinatePoint_hasDerivAt_y t (z u))
    have hz : HasDerivAt z (y1 - y0) u := by
      convert ((hasDerivAt_id u).mul_const (y1 - y0)).const_add y0 using 1 <;>
        first | rfl | ring
    convert hqy.comp u hz using 1 <;> rfl
  have hi : IntervalIntegrable
      (fun u => coordPartial 1 q (coordinatePoint t (z u))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hint : IntervalIntegrable
      (fun u => coordPartial 1 q (coordinatePoint t (z u)) * (y1 - y0)) volume 0 1 :=
    hi.mul_const (y1 - y0)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_mul_const] at hFTC
  have h0 : z 0 = y0 := by dsimp [z]; ring
  have h1 : z 1 = y1 := by dsimp [z]; ring
  rw [h0, h1] at hFTC
  unfold verticalAverageDerivative
  simpa only [z, mul_comm] using hFTC.symm

theorem verticalAverageDerivative_diagonal (q : Coord → ℝ) (t y : ℝ) :
    verticalAverageDerivative q t y y = coordPartial 1 q (coordinatePoint t y) := by
  simp [verticalAverageDerivative]

theorem flow_difference_hasDerivWithinAt {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {y0 y1 : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2)
    (hy0 : y0 t ∈ Icc (-3 : ℝ) 3) (hy1 : y1 t ∈ Icc (-3 : ℝ) 3)
    (hdy0 : HasDerivWithinAt y0 (-q (coordinatePoint t (y0 t))) (Icc (-2 : ℝ) 2) t)
    (hdy1 : HasDerivWithinAt y1 (-q (coordinatePoint t (y1 t))) (Icc (-2 : ℝ) 2) t) :
    HasDerivWithinAt (fun v => y1 v - y0 v)
      (-verticalAverageDerivative q t (y0 t) (y1 t) * (y1 t - y0 t))
      (Icc (-2 : ℝ) 2) t := by
  have he := vertical_secant_identity hq hU hSU ht hy0 hy1
  convert hdy1.sub hdy0 using 1
  first | rfl | nlinarith only [he]

theorem scalar_linear_evolution_formula {a z : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (ha : ContinuousOn a (Ioo (-R) R))
    (hz : ∀ t ∈ Ioo (-R) R, HasDerivAt z (-a t * z t) t)
    {t : ℝ} (ht : t ∈ Ioo (-R) R) :
    z t = z 0 * Real.exp (-(∫ r in 0..t, a r)) := by
  let I (v : ℝ) := ∫ r in 0..v, a r
  have hzero : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hI (v : ℝ) (hv : v ∈ Ioo (-R) R) : HasDerivAt I (a v) v := by
    have hseg : uIcc 0 v ⊆ Ioo (-R) R := by
      intro w hw
      exact ⟨(lt_min hzero.1 hv.1).trans_le hw.1,
        hw.2.trans_lt (max_lt hzero.2 hv.2)⟩
    exact intervalIntegral.integral_hasDerivAt_right (ha.mono hseg).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo ha v hv)
      (ha.continuousAt (isOpen_Ioo.mem_nhds hv))
  have hprod (v : ℝ) (hv : v ∈ Ioo (-R) R) :
      HasDerivAt (fun w => z w * Real.exp (I w)) 0 v := by
    convert (hz v hv).mul ((hI v hv).exp) using 1
    first | rfl | ring
  have heq : z t * Real.exp (I t) = z 0 := by
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-R) R).isPreconnected
      (fun v hv => (hprod v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hprod v hv).deriv) ht hzero
    simpa [I] using hconst
  have he : Real.exp (I t) * Real.exp (-I t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    z t = (z t * Real.exp (I t)) * Real.exp (-I t) := by rw [mul_assoc, he, mul_one]
    _ = z 0 * Real.exp (-I t) := by rw [heq]
    _ = _ := rfl

end SmoothLocal.Flow

end

end OAI
