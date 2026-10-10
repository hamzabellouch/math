import OAI.Geometry.IsometricImmersion.Energy.RectangleSobolevOne
import OAI.Geometry.IsometricImmersion.Energy.MultiplierIntegral

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry SmoothLocal.Weighted

variable {tl tr sb st : ℝ}

theorem rectangle_vertical_integral_intervalIntegrable
    {F : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    IntervalIntegrable (fun t => ∫ s in sb..st, F (boxPoint t s)) volume tl tr := by
  have hi : Integrable (fun p : ℝ × ℝ => F (boxPoint p.1 p.2))
      ((volume.restrict (Ioc tl tr)).prod (volume.restrict (Ioc sb st))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact rectangle_area_integrable hF
  have hj := hi.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  simpa only [intervalIntegral.integral_of_le hs, IntegrableOn] using hj

theorem rectangle_vertical_trace_square_bound
    {F Fs : Coord → ℝ} (ht : tl ≤ tr) (hs : sb < st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hFs : ContinuousOn Fs (closedRectangle tl tr sb st))
    (hd : ∀ t ∈ Icc tl tr, ∀ s ∈ Icc sb st,
      HasDerivAt (fun r => F (boxPoint t r)) (Fs (boxPoint t s)) s)
    {y : ℝ} (hy : y ∈ Icc sb st) :
    (∫ t in tl..tr, F (boxPoint t y) ^ 2) ≤
      (1 + 1 / (st - sb)) * rectangleIntegral tl tr sb st (fun p => F p ^ 2) +
        rectangleIntegral tl tr sb st (fun p => Fs p ^ 2) := by
  have hv (t : ℝ) (ht' : t ∈ Icc tl tr) :
      F (boxPoint t y) ^ 2 ≤
      (1 + 1 / (st - sb)) * (∫ s in sb..st, F (boxPoint t s) ^ 2) +
        ∫ s in sb..st, Fs (boxPoint t s) ^ 2 := by
    have hcF : ContinuousOn (fun s => F (boxPoint t s)) (Icc sb st) :=
      hF.comp (by unfold boxPoint; fun_prop) (fun s hs' => boxPoint_mem ht' hs')
    have hcFs : ContinuousOn (fun s => Fs (boxPoint t s)) (Icc sb st) :=
      hFs.comp (by unfold boxPoint; fun_prop) (fun s hs' => boxPoint_mem ht' hs')
    exact interval_point_square_bound hs hcF hcFs (hd t ht') hy
  have hline : ContinuousOn (fun t => F (boxPoint t y) ^ 2) (Icc tl tr) :=
    (hF.pow 2).comp (by unfold boxPoint; fun_prop) (fun t ht' => boxPoint_mem ht' hy)
  have hIF := rectangle_vertical_integral_intervalIntegrable ht hs.le (hF.pow 2)
  have hIS := rectangle_vertical_integral_intervalIntegrable ht hs.le (hFs.pow 2)
  have hi := intervalIntegral.integral_mono_on ht
    (hline.intervalIntegrable_of_Icc ht)
    ((hIF.const_mul (1 + 1 / (st - sb))).add hIS) hv
  rw [intervalIntegral.integral_add (hIF.const_mul (1 + 1 / (st - sb))) hIS,
    intervalIntegral.integral_const_mul] at hi
  rw [← rectangleIntegral_swap ht hs.le (hF.pow 2),
    ← rectangleIntegral_swap ht hs.le (hFs.pow 2)] at hi
  exact hi

theorem rectangle_point_square_bound
    {f : Coord → ℝ} {U : Set Coord} (ht : tl < tr) (hs : sb < st)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    {x y : ℝ} (hx : x ∈ Icc tl tr) (hy : y ∈ Icc sb st) :
    f (boxPoint x y) ^ 2 ≤
      (1 + 1 / (tr - tl)) * (1 + 1 / (st - sb)) *
        rectangleIntegral tl tr sb st (fun p => f p ^ 2) +
      (1 + 1 / (st - sb)) *
        rectangleIntegral tl tr sb st (fun p => coordPartial 0 f p ^ 2) +
      (1 + 1 / (tr - tl)) *
        rectangleIntegral tl tr sb st (fun p => coordPartial 1 f p ^ 2) +
      rectangleIntegral tl tr sb st (fun p => coordPartial 1 (coordPartial 0 f) p ^ 2) := by
  have hfx := partial_contDiffOn hf hU 0
  have hfy := partial_contDiffOn hf hU 1
  have hfyx := partial_contDiffOn hfx hU 1
  have hfc : ContinuousOn f (closedRectangle tl tr sb st) := hf.continuousOn.mono hbox
  have hfxc : ContinuousOn (coordPartial 0 f) (closedRectangle tl tr sb st) :=
    hfx.continuousOn.mono hbox
  have hfyc : ContinuousOn (coordPartial 1 f) (closedRectangle tl tr sb st) :=
    hfy.continuousOn.mono hbox
  have hfyxc : ContinuousOn (coordPartial 1 (coordPartial 0 f))
      (closedRectangle tl tr sb st) := hfyx.continuousOn.mono hbox
  have hdt (t : ℝ) (ht' : t ∈ Icc tl tr) :
      HasDerivAt (fun r => f (boxPoint r y)) (coordPartial 0 f (boxPoint t y)) t := by
    have hp := hbox (boxPoint_mem ht' hy)
    exact ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt t (boxPoint_hasDerivAt_t t y)
  have hds (t : ℝ) (ht' : t ∈ Icc tl tr) (s : ℝ) (hs' : s ∈ Icc sb st) :
      HasDerivAt (fun r => f (boxPoint t r)) (coordPartial 1 f (boxPoint t s)) s := by
    have hp := hbox (boxPoint_mem ht' hs')
    exact ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
  have hdxs (t : ℝ) (ht' : t ∈ Icc tl tr) (s : ℝ) (hs' : s ∈ Icc sb st) :
      HasDerivAt (fun r => coordPartial 0 f (boxPoint t r))
        (coordPartial 1 (coordPartial 0 f) (boxPoint t s)) s := by
    have hp := hbox (boxPoint_mem ht' hs')
    exact ((hfx.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
  have hhor := interval_point_square_bound ht
    (hfc.comp (by unfold boxPoint; fun_prop) (fun t ht' => boxPoint_mem ht' hy))
    (hfxc.comp (by unfold boxPoint; fun_prop) (fun t ht' => boxPoint_mem ht' hy)) hdt hx
  have hvf := rectangle_vertical_trace_square_bound ht.le hs hfc hfyc hds hy
  have hvx := rectangle_vertical_trace_square_bound ht.le hs hfxc hfyxc hdxs hy
  have hL : 0 ≤ 1 + 1 / (tr - tl) :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (sub_nonneg.mpr ht.le))
  have hscale := mul_le_mul_of_nonneg_left hvf hL
  simp only [Function.comp_def] at hhor
  nlinarith only [hscale, hvx, hhor]

theorem nested_rectangle_square_bound
    {f : Coord → ℝ} {U : Set Coord} {il ir ib it : ℝ}
    (ht : tl < tr) (hs : sb < st) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hinner : closedRectangle il ir ib it ⊆ closedRectangle tl tr sb st)
    {p : Coord} (hp : p ∈ closedRectangle il ir ib it) :
    f p ^ 2 ≤
      (1 + 1 / (tr - tl)) * (1 + 1 / (st - sb)) *
        rectangleIntegral tl tr sb st (fun q => f q ^ 2) +
      (1 + 1 / (st - sb)) *
        rectangleIntegral tl tr sb st (fun q => coordPartial 0 f q ^ 2) +
      (1 + 1 / (tr - tl)) *
        rectangleIntegral tl tr sb st (fun q => coordPartial 1 f q ^ 2) +
      rectangleIntegral tl tr sb st (fun q => coordPartial 1 (coordPartial 0 f) q ^ 2) := by
  have hp' := hinner hp
  have he : boxPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> simp [boxPoint]
  simpa only [he] using rectangle_point_square_bound ht hs hU hf hbox hp'.1 hp'.2

end SmoothLocal.Sobolev

end

end OAI
