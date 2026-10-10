import OAI.Geometry.IsometricImmersion.Flows.FlowSecondVariation

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def initialSecondFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun u => deriv (fun v => Y v p.1) u) p.2

def initialSecondForcing (q : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ r in 0..p.1, coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y p.2 r)) *
    deriv (fun v => Y v r) p.2

def initialThirdForcing (q : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ r in 0..p.1,
    coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y p.2 r)) *
      (deriv (fun v => Y v r) p.2) ^ 2 +
    coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y p.2 r)) *
      deriv (fun u => deriv (fun v => Y v r) u) p.2

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

theorem flowPullback_hasDerivAt_y {C : Coord → ℝ} (hC : ContDiffOn ℝ ∞ C U)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => C (coordinatePoint t (Y u t)))
      (coordPartial 1 C (coordinatePoint t (Y s t)) * deriv (fun u => Y u t) s) s := by
  have hB := flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hC
  have hd : HasFDerivAt (fun p : ℝ × ℝ => C (flowCoordinateMap Y p))
      (fderiv ℝ (fun p : ℝ × ℝ => C (flowCoordinateMap Y p)) (t, s)) (t, s) :=
    ((hB.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨ht, hs⟩)).differentiableAt
      (by simp)).hasFDerivAt
  have hh := hd.comp_hasDerivAt s ((hasDerivAt_const s t).prodMk (hasDerivAt_id s))
  change HasDerivAt (fun u => C (coordinatePoint t (Y u t)))
    (pairPartialY (fun p => C (flowCoordinateMap Y p)) (t, s)) s at hh
  rw [flowPullback_partial_y hq hU hSU hY hrange hstart hode hC ⟨ht, hs⟩] at hh
  exact hh

theorem initialSecondFlowDerivative_contDiffOn :
    ContDiffOn ℝ ∞ (initialSecondFlowDerivative Y) (pairRectangle 2 (-2) 2) := by
  have hV := initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode
  have hd : ContDiffOn ℝ ∞ (pairPartialY (initialFlowDerivative Y))
      (pairRectangle 2 (-2) 2) :=
    (hV.fderiv_of_isOpen (pairRectangle_isOpen 2 (-2) 2) (by simp)).clm_apply contDiffOn_const
  apply hd.congr
  intro p hp
  have hder := ((hV.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt
  exact (hder.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem initialSecondForcing_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => initialSecondForcing q Y (t, u))
      (initialThirdForcing q Y (t, s)) s := by
  let C (p : ℝ × ℝ) := coordPartial 1 (coordPartial 1 q) (flowCoordinateMap Y p) *
    initialFlowDerivative Y p
  have hqq := partial_contDiffOn (partial_contDiffOn hq hU 1) hU 1
  have hC : ContDiffOn ℝ ∞ C (pairRectangle 2 (-2) 2) :=
    (flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hqq).mul
      (initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode)
  have hi := pairPrimitive_hasDerivAt_y (hC.of_le (by simp)) ht hs
  have heq : pairPrimitive (pairPartialY C) (t, s) = initialThirdForcing q Y (t, s) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hz : (0 : ℝ) ∈ Ioo (-2) 2 := by norm_num
    have hr' : r ∈ Ioo (-2 : ℝ) 2 :=
      ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
    have hqder := flowPullback_hasDerivAt_y hq hU hSU hY hrange hstart hode hqq hs hr'
    have hVder := (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs hr').differentiableAt.hasDerivAt
    have hprod := hqder.mul hVder
    have hfd : HasFDerivAt C (fderiv ℝ C (r, s)) (r, s) :=
      ((hC.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨hr', hs⟩)).differentiableAt
        (by simp)).hasFDerivAt
    have he := (hfd.comp_hasDerivAt s
      ((hasDerivAt_const s r).prodMk (hasDerivAt_id s))).unique hprod
    change pairPartialY C (r, s) = _ at he
    change pairPartialY C (r, s) = _
    rw [he]
    ring
  rw [heq] at hi
  exact hi

theorem cap_flow_initial_third_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => initialSecondFlowDerivative Y (t, u))
      (-initialSecondFlowDerivative Y (t, s) * initialSecondForcing q Y (t, s) -
        initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s)) s := by
  have hV : HasDerivAt (fun u => initialFlowDerivative Y (t, u))
      (initialSecondFlowDerivative Y (t, s)) s :=
    (cap_flow_initial_second_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).differentiableAt.hasDerivAt
  have hI := initialSecondForcing_hasDerivAt hq hU hSU hY hrange hstart hode hs ht
  have hproduct : HasDerivAt
      (fun u => -initialFlowDerivative Y (t, u) * initialSecondForcing q Y (t, u))
      (-initialSecondFlowDerivative Y (t, s) * initialSecondForcing q Y (t, s) +
        -initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s)) s := hV.neg.mul hI
  have he : (fun u => initialSecondFlowDerivative Y (t, u)) =ᶠ[𝓝 s]
      (fun u => -initialFlowDerivative Y (t, u) * initialSecondForcing q Y (t, u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact cap_flow_initial_second_formula hq hU hSU hY hrange hstart hode hu ht
  convert hproduct.congr_of_eventuallyEq he using 1
  first | rfl | ring

theorem cap_flow_initial_third_formula {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    deriv (fun u => initialSecondFlowDerivative Y (t, u)) s =
      -initialSecondFlowDerivative Y (t, s) * initialSecondForcing q Y (t, s) -
        initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s) :=
  (cap_flow_initial_third_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

theorem initialThirdForcing_integrable_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    (hMqqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    IntervalIntegrable (fun r =>
      coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y s r)) *
        (deriv (fun v => Y v r) s)^2 +
      coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
        deriv (fun u => deriv (fun v => Y v r) u) s) volume 0 t ∧
    |initialThirdForcing q Y (t, s)| ≤ (2 * M + 4 * M^2) * Real.exp (4 * M) := by
  let C (p : ℝ × ℝ) :=
    coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (flowCoordinateMap Y p) * (initialFlowDerivative Y p)^2 +
    coordPartial 1 (coordPartial 1 q) (flowCoordinateMap Y p) * initialSecondFlowDerivative Y p
  have hqq := partial_contDiffOn (partial_contDiffOn hq hU 1) hU 1
  have hC : ContDiffOn ℝ ∞ C (pairRectangle 2 (-2) 2) :=
    ((flowPullback_contDiffOn hq hU hSU hY hrange hstart hode (partial_contDiffOn hqq hU 1)).mul
      ((initialFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode).pow 2)).add
      ((flowPullback_contDiffOn hq hU hSU hY hrange hstart hode hqq).mul
        (initialSecondFlowDerivative_contDiffOn hq hU hSU hY hrange hstart hode))
  have hc : ContinuousOn (fun r => C (r, s)) (Ioo (-2 : ℝ) 2) :=
    hC.continuousOn.comp (f := fun r => (r, s)) (by fun_prop) (fun r hr => ⟨hr, hs⟩)
  have hseg : uIcc (0 : ℝ) t ⊆ Ioo (-2 : ℝ) 2 := by
    intro r hr
    have hz : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by norm_num
    exact ⟨(lt_min hz.1 ht.1).trans_le hr.1, hr.2.trans_lt (max_lt hz.2 ht.2)⟩
  refine ⟨(hc.mono hseg).intervalIntegrable, ?_⟩
  have hbound (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) t) :
      ‖C (r, s)‖ ≤ (M + 2 * M^2) * Real.exp (4 * M) := by
    have hr' := hseg hr
    have hp := flowCoordinateMap_mem_modelSquare (p := (r, s)) hq hU hSU hY hrange hstart hode ⟨hr', hs⟩
    have hV := (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs hr').2
    have hVpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs hr'
    have hVsq : |(deriv (fun v => Y v r) s)^2| ≤ Real.exp (4 * M) := by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ (Real.exp (2 * M))^2 := pow_le_pow_left₀ hVpos.le hV 2
        _ = Real.exp (4 * M) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    have hW := cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs hr'
    rw [Real.norm_eq_abs]
    calc
      |C (r, s)| ≤
          |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y s r))| *
            |(deriv (fun v => Y v r) s)^2| +
          |coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r))| *
            |deriv (fun u => deriv (fun v => Y v r) u) s| := by
        calc
          _ ≤ |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) (coordinatePoint r (Y s r)) *
              (deriv (fun v => Y v r) s)^2| +
              |coordPartial 1 (coordPartial 1 q) (coordinatePoint r (Y s r)) *
                deriv (fun u => deriv (fun v => Y v r) u) s| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ M * Real.exp (4 * M) + M * (2 * M * Real.exp (4 * M)) :=
        add_le_add (mul_le_mul (hMqqq _ hp) hVsq (abs_nonneg _) hM)
          (mul_le_mul (hMqq _ hp) hW (abs_nonneg _) hM)
      _ = (M + 2 * M^2) * Real.exp (4 * M) := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := (M + 2 * M^2) * Real.exp (4 * M)) (f := fun r => C (r, s))
    (fun r hr => hbound r (uIoc_subset_uIcc hr))
  have ht2 : |t| ≤ 2 := (abs_lt.mpr ht).le
  calc
    _ ≤ ((M + 2 * M^2) * Real.exp (4 * M)) * |t| := by
      simpa only [Real.norm_eq_abs, sub_zero, initialThirdForcing, C,
        flowCoordinateMap, initialFlowDerivative, initialSecondFlowDerivative] using hi
    _ ≤ ((M + 2 * M^2) * Real.exp (4 * M)) * 2 := mul_le_mul_of_nonneg_left ht2
      (mul_nonneg (by positivity) (Real.exp_pos _).le)
    _ = (2 * M + 4 * M^2) * Real.exp (4 * M) := by ring

theorem cap_flow_initial_third_bound {M : ℝ} (hM : 0 ≤ M)
    (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hMqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 q) p| ≤ M)
    (hMqqq : ∀ p ∈ modelSquare, |coordPartial 1 (coordPartial 1 (coordPartial 1 q)) p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |deriv (fun u => initialSecondFlowDerivative Y (t, u)) s| ≤
      (2 * M + 8 * M^2) * Real.exp (6 * M) := by
  rw [cap_flow_initial_third_formula hq hU hSU hY hrange hstart hode hs ht]
  have hW := cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs ht
  have hI := (flow_initial_second_integral_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hs ht).2
  have hJ := (initialThirdForcing_integrable_bound hq hU hSU hY hrange hstart hode hM hMq hMqq hMqqq hs ht).2
  have hV : |initialFlowDerivative Y (t, s)| ≤ Real.exp (2 * M) := by
    unfold initialFlowDerivative
    rw [abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hs ht)]
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hs ht).2
  calc
    _ ≤ |initialSecondFlowDerivative Y (t, s)| * |initialSecondForcing q Y (t, s)| +
        |initialFlowDerivative Y (t, s)| * |initialThirdForcing q Y (t, s)| := by
      simpa only [abs_mul, abs_neg] using
        abs_sub (-(initialSecondFlowDerivative Y (t, s)) * initialSecondForcing q Y (t, s))
          (initialFlowDerivative Y (t, s) * initialThirdForcing q Y (t, s))
    _ ≤ (2 * M * Real.exp (4 * M)) * (2 * M * Real.exp (2 * M)) +
        Real.exp (2 * M) * ((2 * M + 4 * M^2) * Real.exp (4 * M)) :=
      add_le_add (mul_le_mul hW hI (abs_nonneg _) (by positivity))
        (mul_le_mul hV hJ (abs_nonneg _) (Real.exp_pos _).le)
    _ = (2 * M + 8 * M^2) * (Real.exp (2 * M) * Real.exp (4 * M)) := by ring
    _ = (2 * M + 8 * M^2) * Real.exp (6 * M) := by
      rw [← Real.exp_add]
      congr 2
      ring

end ActualFlow
end SmoothLocal.Flow

end

end OAI
