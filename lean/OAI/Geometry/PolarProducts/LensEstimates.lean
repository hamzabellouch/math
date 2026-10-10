import OAI.Geometry.PolarProducts.LensArea

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
open Set Filter Complex MeasureTheory intervalIntegral
open scoped Topology ContDiff
noncomputable section

theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) := by
    apply continuous_const.div (by fun_prop)
    intro t; positivity
  have hi := integral_mono_on (μ := volume) hx (hc.intervalIntegrable 0 x)
    (intervalIntegrable_const (c := (1 : ℝ))) (fun t _ => by
      apply (div_le_one (by positivity : 0 < 1+t^2)).mpr
      nlinarith [sq_nonneg t])
  simpa [integral_one_div_one_add_sq] using hi

theorem half_le_arctan {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x/2 ≤ Real.arctan x := by
  have hc : Continuous (fun t : ℝ => 1/(1+t^2)) := by
    apply continuous_const.div (by fun_prop)
    intro t; positivity
  have hi := integral_mono_on (μ := volume) hx (intervalIntegrable_const (c := (1/2 : ℝ)))
    (hc.intervalIntegrable 0 x) (fun t ht => by
      apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr
      have h0 := ht.1
      have h1 := ht.2.trans hx1
      nlinarith)
  simpa [integral_one_div_one_add_sq, div_eq_mul_inv] using hi

theorem reciprocal_arctan {x : ℝ} (hx : 0 < x) :
    1 / Real.arctan x ≤ 2 / Real.pi + 2/x := by
  have ha : 0 < Real.arctan x := Real.arctan_pos.mpr hx
  rcases le_total x 1 with hx1 | hx1
  · have hh := half_le_arctan hx.le hx1
    have hdiv : 1 / Real.arctan x ≤ 2/x := by
      apply (div_le_div_iff₀ ha hx).mpr
      linarith
    apply hdiv.trans
    have hp : 0 < 2 / Real.pi := by positivity
    linarith
  · have hh : Real.pi / 2 - Real.arctan x ≤ 1/x := by
      rw [← Real.arctan_inv_of_pos hx]
      simpa only [one_div] using arctan_le_self (inv_nonneg.mpr hx.le)
    have hA : Real.pi / 4 ≤ Real.arctan x := by
      simpa using Real.arctan_strictMono.monotone hx1
    have hπA : 1 ≤ Real.pi * Real.arctan x := by
      have hp := Real.pi_gt_three
      nlinarith [mul_le_mul_of_nonneg_left hA Real.pi_pos.le]
    have hfirst : (Real.pi/2-Real.arctan x) / Real.arctan x ≤ (1/x)/Real.arctan x :=
      div_le_div_of_nonneg_right hh ha.le
    have hsecond : (2/Real.pi)*((1/x)/Real.arctan x) ≤ 2/x := by
      apply (le_div_iff₀ hx).mpr
      have he : (2/Real.pi)*((1/x)/Real.arctan x)*x = 2/(Real.pi*Real.arctan x) := by
        field_simp
      rw [he]
      apply (div_le_iff₀ (mul_pos Real.pi_pos ha)).mpr
      linarith
    have hthird := mul_le_mul_of_nonneg_left hfirst
      (by positivity : 0 ≤ 2/Real.pi)
    have he : (2/Real.pi)*((Real.pi/2-Real.arctan x)/Real.arctan x) =
        1/Real.arctan x - 2/Real.pi := by field_simp
    rw [he] at hthird
    linarith

def circleTop (r s : ℝ) : ℂ := (r : ℂ) * ((Real.sin s : ℂ)+(Real.cos s : ℂ)*I)

@[simp] theorem circleTop_re (r s : ℝ) : (circleTop r s).re = r * Real.sin s := by
  simp only [circleTop, mul_re, add_re, ofReal_re, ofReal_im, I_im, I_re,
    mul_zero, mul_one, sub_zero, zero_mul, add_zero]

@[simp] theorem circleTop_im (r s : ℝ) : (circleTop r s).im = r * Real.cos s := by
  simp only [circleTop, mul_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, I_im, I_re,
    mul_zero, mul_one, zero_add, zero_mul, add_zero]

theorem norm_circleTop (r s : ℝ) : ‖circleTop r s‖ = |r| := by
  have hh : ‖circleTop r s‖^2 = r^2 := by
    rw [Complex.sq_norm, normSq_apply, circleTop_re, circleTop_im]
    nlinarith [Real.sin_sq_add_cos_sq s]
  nlinarith [sq_abs r, norm_nonneg (circleTop r s), abs_nonneg r]

@[simp] theorem circleTop_zero (r : ℝ) : circleTop r 0 = (r : ℂ)*I := by
  simp [circleTop]

@[simp] theorem circleTop_pi_half (r : ℝ) : circleTop r (Real.pi/2) = (r : ℂ) := by
  simp [circleTop]

theorem continuous_circleTop (r : ℝ) : Continuous (circleTop r) := by
  unfold circleTop; fun_prop

theorem hasDerivAt_F_im_circleTop {r : ℝ} (hr : |r| < 1) (s : ℝ) :
    HasDerivAt (fun s => (F (circleTop r s)).im) (-A (circleTop r s)) s := by
  have hnorm : ‖(r : ℂ)*(Complex.sin s+Complex.cos s*I)‖ < 1 := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    change ‖circleTop r s‖ < 1
    rw [norm_circleTop]
    exact hr
  have hd := ((Complex.hasDerivAt_sin (s : ℂ)).add
    ((Complex.hasDerivAt_cos (s : ℂ)).mul_const I)).const_mul (r : ℂ)
  have hf := (hasDerivAt_F hnorm).differentiableAt.hasDerivAt
  have hh := hf.comp (s : ℂ) hd
  have hm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hh.comp_ofReal
  convert hm using 1 <;> try rfl
  · funext x
    simp only [circleTop, ofReal_sin, ofReal_cos, Function.comp_apply, Pi.add_apply,
      Complex.imCLM_apply]
  · simp only [Complex.imCLM_apply, A, circleTop, ← ofReal_sin, ← ofReal_cos,
      mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, add_zero, zero_add, zero_sub, neg_re, neg_im]
    ring

theorem continuous_A_circleTop {r : ℝ} (hr : |r| < 1) :
    Continuous (fun s => A (circleTop r s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hs : circleTop r s ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, norm_circleTop] using hr
  exact Complex.continuous_re.continuousAt.comp
    (((continuous_circleTop r).continuousAt).mul
      (((analyticOnNhd_F _ hs).deriv.continuousAt).comp (continuous_circleTop r).continuousAt))

theorem gap_integral {r : ℝ} (hr : |r| < 1) (s : ℝ) :
    T r - (F (circleTop r s)).im = ∫ x in 0..s, A (circleTop r x) := by
  have hh := integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_F_im_circleTop hr x)
    ((continuous_A_circleTop hr).neg.intervalIntegrable 0 s)
  rw [intervalIntegral.integral_neg, circleTop_zero] at hh
  change -(∫ x in 0..s, A (circleTop r x)) = (F (circleTop r s)).im - T r at hh
  linarith

theorem A_circleTop_le {r s : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : 0 ≤ s) (hs1 : s ≤ Real.pi/2) :
    A (circleTop r s) ≤ (8*r/(Real.pi^2*(1-r^2)))*s := by
  have hrabs : |r| < 1 := by simpa only [abs_of_nonneg hr] using hr1
  have hnorm : ‖circleTop r s‖ < 1 := by simpa only [norm_circleTop] using hrabs
  rw [A, re_mul_deriv_F hnorm, circleTop_re, norm_circleTop, sq_abs]
  have hd : 0 < 1-r^2 := by nlinarith
  have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_mem_Icc ⟨hs, by linarith [Real.pi_pos]⟩
  have hx : 0 ≤ 2*(r*Real.sin s)/(1-r^2) := by positivity
  calc
    _ ≤ (4/Real.pi^2) * (2*(r*Real.sin s)/(1-r^2)) := by
      exact mul_le_mul_of_nonneg_left (arctan_le_self hx) (by positivity)
    _ ≤ (4/Real.pi^2) * (2*(r*s)/(1-r^2)) := by
      gcongr
      exact Real.sin_le hs
    _ = _ := by field_simp; ring

theorem gap_le_square {r s : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : 0 ≤ s) (hs1 : s ≤ Real.pi/2) :
    T r - (F (circleTop r s)).im ≤ s^2/(1-r) := by
  have hrabs : |r| < 1 := by simpa only [abs_of_nonneg hr] using hr1
  rw [gap_integral hrabs]
  have hh := integral_mono_on (μ := volume) hs ((continuous_A_circleTop hrabs).intervalIntegrable 0 s)
    ((show Continuous (fun x : ℝ => (8*r/(Real.pi^2*(1-r^2)))*x) from by fun_prop).intervalIntegrable 0 s)
    (fun x hx => A_circleTop_le hr hr1 hx.1 (hx.2.trans hs1))
  have he : (∫ x in 0..s, (8*r/(Real.pi^2*(1-r^2)))*x) =
      (4*r/(Real.pi^2*(1-r^2)))*s^2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [he] at hh
  apply hh.trans
  have hd : 0 < 1-r^2 := by nlinarith
  have h1 : 0 < 1-r := by linarith
  have hco : 4*r/(Real.pi^2*(1-r^2)) ≤ 1/(1-r) := by
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos Real.pi_pos) hd) h1).mpr
    have hp := Real.pi_gt_three
    have heq : 1-r^2 = (1-r)*(1+r) := by ring
    rw [heq]
    have haux : 4*r ≤ Real.pi^2*(1+r) := by
      have hp4 : 0 ≤ Real.pi^2-4 := by nlinarith
      nlinarith [mul_nonneg hp4 hr]
    nlinarith [mul_nonneg (sub_nonneg.mpr haux) h1.le]
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using mul_le_mul_of_nonneg_right hco (sq_nonneg s)

theorem reciprocal_A_circleTop {r s : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1)
    (hs : 0 < s) (hs1 : s ≤ Real.pi/2) :
    1 / A (circleTop r s) ≤ Real.pi/2 + Real.pi^3*(1-r)/s := by
  have hr0 : 0 < r := by linarith
  have hd : 0 < 1-r^2 := by nlinarith
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs (by linarith [Real.pi_pos])
  have hnorm : ‖circleTop r s‖ < 1 := by simpa [norm_circleTop, abs_of_pos hr0] using hr1
  let X := 2*(r*Real.sin s)/(1-r^2)
  have hX : 0 < X := by dsimp [X]; positivity
  have hA : 0 < Real.arctan X := Real.arctan_pos.mpr hX
  have he : 1 / A (circleTop r s) = (Real.pi^2/4) * (1/Real.arctan X) := by
    rw [A, re_mul_deriv_F hnorm, circleTop_re, norm_circleTop, sq_abs]
    dsimp [X]
    field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (reciprocal_arctan hX)
    (by positivity : 0 ≤ Real.pi^2/4)
  apply hh.trans
  have hratio : (1+r)/r ≤ 4 := by
    apply (div_le_iff₀ hr0).mpr
    linarith
  have hsinbound : (1-r)/Real.sin s ≤ (Real.pi/2)*((1-r)/s) := by
    apply (div_le_iff₀ hsin).mpr
    have hx := Real.mul_le_sin hs.le hs1
    have hy : s ≤ (Real.pi/2)*Real.sin s := by
      have hp := mul_le_mul_of_nonneg_left hx (Real.pi_pos.le)
      field_simp at hp
      linarith
    have hz := mul_le_mul_of_nonneg_left hy (show 0 ≤ (1-r)/s by positivity)
    have heq : (1-r)/s*s = 1-r := by field_simp
    rw [heq] at hz
    nlinarith
  calc
    _ = Real.pi/2 + (Real.pi^2/4)*((1+r)/r)*((1-r)/Real.sin s) := by
      dsimp [X]
      field_simp
      ring
    _ ≤ Real.pi/2 + Real.pi^2*((1-r)/Real.sin s) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left hratio (show 0 ≤ Real.pi^2/4 by positivity)]
    _ ≤ Real.pi/2 + Real.pi^2*((Real.pi/2)*((1-r)/s)) := by gcongr
    _ ≤ Real.pi/2 + Real.pi^3*(1-r)/s := by
      have hp : 0 ≤ Real.pi^3*(1-r)/s := by positivity
      have heq : Real.pi^2*((Real.pi/2)*((1-r)/s)) =
          (Real.pi^3*(1-r)/s)/2 := by ring
      rw [heq]
      linarith

theorem circleTop_arg {w : ℂ} (hr : 0 < w.re) (hi : 0 ≤ w.im) :
    ∃ s ∈ Ioc (0 : ℝ) (Real.pi/2), circleTop ‖w‖ s = w := by
  let s := Real.pi/2-w.arg
  have ha0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hi
  have ha1 : w.arg < Real.pi/2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hr)
  refine ⟨s, ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩, ?_⟩
  apply Complex.ext
  · rw [circleTop_re]
    dsimp [s]
    rw [Real.sin_pi_div_two_sub, Complex.norm_mul_cos_arg]
  · rw [circleTop_im]
    dsimp [s]
    rw [Real.cos_pi_div_two_sub, Complex.norm_mul_sin_arg]

lemma div_le_sqrt_of_gap {d δ s : ℝ} (hd : 0 < d) (hδ : 0 < δ) (hs : 0 < s)
    (hg : δ ≤ s^2/d) : d/s ≤ Real.sqrt (d/δ) := by
  have hg' : δ*d ≤ s^2 := (le_div_iff₀ hd).mp hg
  have he : (d/s)^2 ≤ d/δ := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hs) hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hg' hd.le]
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr he

theorem reciprocal_A_slice {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re)
    (hradius : 1/2 ≤ ‖w‖) :
    1 / A w ≤ Real.pi/2 + Real.pi^3 *
      Real.sqrt ((1-‖w‖)/(T ‖w‖ - |(F w).im|)) := by
  have hFw : F w ∈ D := ⟨w, by simpa using hw, rfl⟩
  have hdelta : 0 < T ‖w‖ - |(F w).im| := by
    have hh := vertical_gap_pos hFw (re_F_pos hw hr)
    simpa only [g_F hw] using hh
  have upper (z : ℂ) (hz : ‖z‖ < 1) (hzr : 0 < z.re) (hzi : 0 ≤ z.im)
      (hzlow : 1/2 ≤ ‖z‖) (hgap : 0 < T ‖z‖ - |(F z).im|) :
      1 / A z ≤ Real.pi/2 + Real.pi^3 *
        Real.sqrt ((1-‖z‖)/(T ‖z‖ - |(F z).im|)) := by
    obtain ⟨s, hs, he⟩ := circleTop_arg hzr hzi
    have hh := reciprocal_A_circleTop hzlow hz hs.1 hs.2
    rw [he] at hh
    apply hh.trans
    have hgs := gap_le_square (norm_nonneg z) hz hs.1.le hs.2
    rw [he] at hgs
    have hg : T ‖z‖ - |(F z).im| ≤ s^2/(1-‖z‖) := by
      linarith [le_abs_self (F z).im]
    have hb := div_le_sqrt_of_gap (sub_pos.mpr hz) hgap hs.1 hg
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ Real.pi^3 by positivity)
    have heq : Real.pi^3*((1-‖z‖)/s) = Real.pi^3*(1-‖z‖)/s := by ring
    rw [heq] at hm
    linarith
  rcases le_total 0 w.im with hi | hi
  · exact upper w hw hr hi hradius hdelta
  · have hn : ‖(starRingEnd ℂ) w‖ = ‖w‖ := by simp
    have ha : A ((starRingEnd ℂ) w) = A w := by
      rw [A, re_mul_deriv_F (by simpa using hw), A, re_mul_deriv_F hw]
      simp
    have hh := upper ((starRingEnd ℂ) w) (by simpa using hw) (by simpa using hr)
      (by simpa using neg_nonneg.mpr hi) (by simpa using hradius) (by simpa using hdelta)
    simpa [ha] using hh

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem deriv_T_eq {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    deriv T r = (8 / Real.pi^2) * (Real.artanh r / r) := by
  have habs : |r| < 1 := by simpa only [abs_of_pos hr] using hr1
  rw [(hasDerivAt_T habs).deriv]
  have hh := congr_arg Complex.im (mul_deriv_F (w := (r : ℂ)*I) (by simpa [norm_mul] using habs))
  have hc : cayley ((r : ℂ)*I) = (((1-r)/(1+r) : ℝ) : ℂ) := by
    unfold cayley
    push_cast
    rw [mul_assoc, I_mul_I]
    ring
  have hai : (Complex.arctan ((r : ℂ)*I)).im = Real.artanh r := by
    rw [Complex.arctan]
    change ((-I/2) * Complex.log (cayley ((r : ℂ)*I))).im = _
    rw [hc, mul_im]
    have hp : 0 < (1-r)/(1+r) := by positivity
    have hre : (-I/2 : ℂ).re = 0 := by norm_num [div_re]
    have him : (-I/2 : ℂ).im = -1/2 := by norm_num [div_im]
    rw [hre, him, zero_mul, zero_add]
    rw [Complex.log_re, norm_real, Real.norm_eq_abs, abs_of_pos hp,
      Real.artanh_eq_half_log ⟨by linarith, hr1.le⟩]
    have hlog : Real.log ((1-r)/(1+r)) = -Real.log ((1+r)/(1-r)) := by
      rw [show (1-r)/(1+r) = ((1+r)/(1-r))⁻¹ by rw [inv_div], Real.log_inv]
    rw [hlog]
    norm_num
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    zero_mul, zero_sub, add_zero, neg_zero, zero_add] at hh
  rw [hai] at hh
  rw [mul_comm] at hh
  have hh := (eq_div_iff hr.ne').mpr hh
  calc
    _ = ((8 / Real.pi^2) * Real.artanh r)/r := hh
    _ = _ := by ring

theorem deriv_T_lower {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (hr : r < 1) :
    (8/Real.pi^2) * Real.artanh a ≤ deriv T r := by
  have hr0 : 0 < r := ha.trans_le har
  rw [deriv_T_eq hr0 hr]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (Real.artanh_le_artanh (by linarith) hr har).trans
  exact le_div_self (Real.artanh_nonneg hr0.le) hr0 hr.le

theorem T_tail_gap {a r s : ℝ} (ha : 0 < a) (har : a ≤ r) (hrs : r ≤ s)
    (hs : s < 1) :
    (8/Real.pi^2)*Real.artanh a * (s-r) ≤ T s-T r := by
  apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc r s)
    (continuousOn_T.mono (by intro x hx; exact ⟨by linarith [hx.1], hx.2.trans hs.le⟩))
    (by intro x hx
        have hxabs : |x| < 1 := by
          simp only [interior_Icc, mem_Ioo] at hx
          exact abs_lt.mpr ⟨by linarith, by linarith⟩
        exact (hasDerivAt_T hxabs).differentiableAt.differentiableWithinAt)
    (by intro x hx
        simp only [interior_Icc, mem_Ioo] at hx
        exact deriv_T_lower ha (har.trans hx.1.le) (hx.2.trans hs))
    r ⟨le_rfl, hrs⟩ s ⟨hrs, le_rfl⟩ hrs

theorem exists_tail_cutoff (M : ℝ) : ∃ a ∈ Ioo (1/2 : ℝ) 1,
    M < (8/Real.pi^2)*Real.artanh a := by
  let y := max (Real.artanh (1/2)) ((Real.pi^2/8)*M) + 1
  let a := Real.tanh y
  have ha : a ∈ Ioo (-1 : ℝ) 1 := ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩
  have hy : Real.artanh a = y := Real.artanh_tanh y
  have hhalf : (1/2 : ℝ) < a := by
    apply (Real.artanh_lt_artanh_iff (by norm_num) ha).mp
    rw [hy]
    dsimp [y]
    have := le_max_left (Real.artanh (1/2)) ((Real.pi^2/8)*M)
    linarith
  refine ⟨a, ⟨hhalf, ha.2⟩, ?_⟩
  rw [hy]
  have hyy : (Real.pi^2/8)*M < y := by
    dsimp [y]
    have := le_max_right (Real.artanh (1/2)) ((Real.pi^2/8)*M)
    linarith
  have hm := mul_lt_mul_of_pos_left hyy (by positivity : 0 < 8/Real.pi^2)
  have he : (8/Real.pi^2)*((Real.pi^2/8)*M) = M := by field_simp
  rwa [he] at hm

end
end PlanarLens

end LowerBoundInline

end OAI
