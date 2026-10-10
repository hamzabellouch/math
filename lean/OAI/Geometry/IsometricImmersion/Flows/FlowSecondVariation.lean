import OAI.Geometry.IsometricImmersion.Flows.FlowBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def initialFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun s => Y s p.1) p.2

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem flowCoordinateMap_mem_modelSquare {p : ℝ × ℝ}
    (hp : p ∈ pairRectangle 2 (-2) 2) : flowCoordinateMap Y p ∈ modelSquare := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hbound : Y p.2 p.1 ∈ Icc (-3 : ℝ) 3 := by
    apply isClosed_Icc.mem_of_tendsto
      (hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).continuousAt
    filter_upwards [(pairRectangle_isOpen 2 (-2) 2).mem_nhds hp] with point hpoint
    exact hrange point.2 ⟨hpoint.2.1.le, hpoint.2.2.le⟩
      point.1 ⟨hpoint.1.1.le, hpoint.1.2.le⟩
  exact coordinatePoint_mem_modelSquare ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    hbound

theorem flowPullback_contDiffOn {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (fun p => C (flowCoordinateMap Y p)) (pairRectangle 2 (-2) 2) := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hT : ContDiffOn ℝ ∞ (flowCoordinateMap Y) (pairRectangle 2 (-2) 2) :=
    (contDiffOn_fst.smul contDiffOn_const).add (hF.smul contDiffOn_const)
  exact hC.comp hT (fun p hp => hSU
    (flowCoordinateMap_mem_modelSquare hq hU hSU hY hrange hstart hode hp))

theorem initialFlowDerivative_eq_pairPartialY {p : ℝ × ℝ}
    (hp : p ∈ pairRectangle 2 (-2) 2) :
    initialFlowDerivative Y p = pairPartialY (fun v : ℝ × ℝ => Y v.2 v.1) p := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hd := ((hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt
  exact (hd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem initialFlowDerivative_contDiffOn :
    ContDiffOn ℝ ∞ (initialFlowDerivative Y) (pairRectangle 2 (-2) 2) := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hd : ContDiffOn ℝ ∞ (pairPartialY (fun v : ℝ × ℝ => Y v.2 v.1))
      (pairRectangle 2 (-2) 2) :=
    (hF.fderiv_of_isOpen (pairRectangle_isOpen 2 (-2) 2) (by simp)).clm_apply contDiffOn_const
  exact hd.congr (fun p hp => initialFlowDerivative_eq_pairPartialY
    hq hU hSU hY hrange hstart hode hp)

theorem flowPullback_partial_y {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U)
    {p : ℝ × ℝ} (hp : p ∈ pairRectangle 2 (-2) 2) :
    pairPartialY (fun v => C (flowCoordinateMap Y v)) p =
      coordPartial 1 C (flowCoordinateMap Y p) * initialFlowDerivative Y p := by
  have hsY : HasDerivAt (fun s => Y s p.1) (initialFlowDerivative Y p) p.2 :=
    (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1).differentiableAt.hasDerivAt
  have hsT : HasDerivAt (fun s => flowCoordinateMap Y (p.1, s))
      (initialFlowDerivative Y p • Pi.single 1 (1 : ℝ)) p.2 := by
    convert
      ((hasDerivAt_const p.2 p.1).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
        (hsY.smul_const (Pi.single 1 (1 : ℝ) : Coord)) using 1 <;>
      first | rfl | simp
  have hmem := hSU (flowCoordinateMap_mem_modelSquare hq hU hSU hY hrange hstart hode hp)
  have hdC := ((hC.contDiffAt (hU.mem_nhds hmem)).differentiableAt (by simp)).hasFDerivAt
  have hchain : HasDerivAt (fun s => C (flowCoordinateMap Y (p.1, s)))
      (coordPartial 1 C (flowCoordinateMap Y p) * initialFlowDerivative Y p) p.2 := by
    convert hdC.comp_hasDerivAt p.2 hsT using 1 <;>
      first | rfl | simp only [map_smul, smul_eq_mul, coordPartial, mul_comm]
  have hB := flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hC
  have hdB : HasFDerivAt (fun v : ℝ × ℝ => C (flowCoordinateMap Y v))
      (fderiv ℝ (fun v : ℝ × ℝ => C (flowCoordinateMap Y v)) p) p :=
    ((hB.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt
  have hpair : HasDerivAt (fun s => C (flowCoordinateMap Y (p.1, s)))
      (pairPartialY (fun v => C (flowCoordinateMap Y v)) p) p.2 := by
    convert hdB.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)) using 1 <;> rfl
  exact hpair.unique hchain

theorem cap_flow_initial_second_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => deriv (fun v => Y v t) u)
      (-deriv (fun v => Y v t) s *
        (∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
          deriv (fun v => Y v r) s)) s := by
  let B (p : ℝ × ℝ) := coordPartial 1 q (flowCoordinateMap Y p)
  have hB : ContDiffOn ℝ ∞ B (pairRectangle 2 (-2) 2) :=
    flowPullback_contDiffOn hq hU hSU hY hrange hstart hode (partial_contDiffOn hq hU 1)
  have hI := pairPrimitive_hasDerivAt_y (hB.of_le (by simp)) ht hs
  have hdiag : pairPrimitive (pairPartialY B) (t, s) =
      ∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
        deriv (fun v => Y v r) s := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Ioo (-2 : ℝ) 2 := by
      have hz : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
      exact ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
    exact flowPullback_partial_y hq hU hSU hY hrange hstart hode
      (partial_contDiffOn hq hU 1) ⟨hr', hs⟩
  have hV : HasDerivAt (fun u => Real.exp (-pairPrimitive B (t, u)))
      (Real.exp (-pairPrimitive B (t, s)) * -pairPrimitive (pairPartialY B) (t, s)) s := hI.neg.exp
  have he : (fun u => deriv (fun v => Y v t) u) =ᶠ[𝓝 s]
      (fun u => Real.exp (-pairPrimitive B (t, u))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hu ht).deriv
  have hVs : Real.exp (-pairPrimitive B (t, s)) = deriv (fun v => Y v t) s :=
    (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).deriv.symm
  rw [hdiag, hVs] at hV
  convert hV.congr_of_eventuallyEq he using 1
  first | rfl | ring

theorem cap_flow_initial_second_formula {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    deriv (fun u => deriv (fun v => Y v t) u) s =
      -deriv (fun v => Y v t) s *
        (∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
          deriv (fun v => Y v r) s) :=
  (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem flow_initial_second_integral_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    IntervalIntegrable (fun r => coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
      deriv (fun v => Y v r) s) volume 0 t ∧
    |∫ r in 0..t, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
      deriv (fun v => Y v r) s| ≤ 2 * M * Real.exp (2 * M) := by
  let C (p : ℝ × ℝ) := coordPartial 1 (coordPartial 1 q) (flowCoordinateMap Y p) * initialFlowDerivative Y p
  have hC : ContDiffOn ℝ ∞ C (pairRectangle 2 (-2) 2) :=
    (flowPullback_contDiffOn hq hU hSU hY hrange hstart hode
      (partial_contDiffOn (partial_contDiffOn hq hU 1) hU 1)).mul
      (initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode)
  have hc : ContinuousOn (fun r => C (r, s)) (Ioo (-2 : ℝ) 2) :=
    hC.continuousOn.comp (f := fun r => (r, s)) (by fun_prop) (fun r hr => ⟨hr, hs⟩)
  have hseg : uIcc (0 : ℝ) t ⊆ Ioo (-2 : ℝ) 2 := by
    intro r hr
    have hz : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
    exact ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
  refine ⟨(hc.mono hseg).intervalIntegrable, ?_⟩
  have hbound (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) t) :
      ‖coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) * deriv (fun v => Y v r) s‖ ≤
        M * Real.exp (2 * M) := by
    have hr' := hseg hr
    have hys := cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs hr'
    have hpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs hr'
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    exact mul_le_mul (hMqq _ (flowCoordinateMap_mem_modelSquare (p := (r, s)) hq hU hSU hY hrange hstart hode
      ⟨hr', hs⟩)) hys.2 hpos.le hM
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := M * Real.exp (2 * M))
    (fun r hr => hbound r (uIoc_subset_uIcc hr))
  have ht2 : |t| ≤ 2 := (abs_lt.mpr ht).le
  calc
    _ ≤ (M * Real.exp (2 * M)) * |t| := by simpa only [Real.norm_eq_abs, sub_zero] using hi
    _ ≤ (M * Real.exp (2 * M)) * 2 := mul_le_mul_of_nonneg_left ht2
      (mul_nonneg hM (Real.exp_pos _).le)
    _ = 2 * M * Real.exp (2 * M) := by ring

theorem cap_flow_initial_second_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => deriv (fun v => Y v t) u) s| ≤ 2 * M * Real.exp (4 * M) := by
  rw [cap_flow_initial_second_formula hq hU hSU hY hrange hstart hode hs ht, abs_mul,
    abs_neg, abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
  calc
    _ ≤ Real.exp (2 * M) * (2 * M * Real.exp (2 * M)) :=
      mul_le_mul (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs ht).2
        (flow_initial_second_integral_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs ht).2
        (abs_nonneg _) (Real.exp_pos _).le
    _ = (2 * M) * (Real.exp (2 * M) * Real.exp (2 * M)) := by ring
    _ = 2 * M * Real.exp (4 * M) := by
      rw [← Real.exp_add]
      congr 2
      ring

end ActualFlow
end SmoothLocal.Flow

end

end OAI
