import OAI.Geometry.PolarProducts.LensMap

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
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

def D : Set ℂ := F '' Metric.ball 0 1

def g : ℂ → ℂ := Function.invFunOn F (Metric.ball 0 1)

theorem g_F {w : ℂ} (hw : ‖w‖ < 1) : g (F w) = w :=
  F_injOn.leftInvOn_invFunOn (by simpa using hw)

theorem F_g {z : ℂ} (hz : z ∈ D) : F (g z) = z :=
  Function.invFunOn_eq hz

theorem norm_g_lt {z : ℂ} (hz : z ∈ D) : ‖g z‖ < 1 := by
  have h := Function.invFunOn_mem hz
  simpa [g] using h

theorem zero_mem_D : (0 : ℂ) ∈ D := ⟨0, by simp, F_zero⟩

@[simp] theorem g_zero : g 0 = 0 := by
  simpa using g_F (by simp : ‖(0 : ℂ)‖ < 1)

theorem g_eq_zero_iff {z : ℂ} (hz : z ∈ D) : g z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [← F_g hz, h, F_zero]
  · rintro rfl; exact g_zero

theorem deriv_F_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : deriv F w ≠ 0 := by
  intro h
  have hh := deriv_F_re_pos hw
  rw [h, zero_re] at hh
  exact lt_irrefl _ hh

theorem analyticOnNhd_g : AnalyticOnNhd ℂ g D := by
  rintro z ⟨w, hw, rfl⟩
  have hw' : ‖w‖ < 1 := by simpa using hw
  apply (analyticAt_comp_iff_of_deriv_ne_zero (analyticOnNhd_F w hw)
    (deriv_F_ne_zero hw')).mp
  apply analyticAt_id.congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
  exact (g_F (by simpa using hv)).symm

theorem isOpen_D : IsOpen D := by
  rcases analyticOnNhd_F.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with h | h
  · obtain ⟨c, hc⟩ := h
    have hz : (0 : ℂ) ∈ Metric.ball 0 1 := by simp
    have hh : (1/2 : ℂ) ∈ Metric.ball 0 1 := by norm_num [Metric.mem_ball, norm_div]
    have he := F_injOn hz hh ((hc 0 hz).trans (hc _ hh).symm)
    norm_num at he
  · exact h _ Subset.rfl Metric.isOpen_ball

theorem isBounded_D : Bornology.IsBounded D := by
  apply ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn continuousOn_F_closedBall).isBounded.subset
  exact image_mono Metric.ball_subset_closedBall

theorem continuousOn_g : ContinuousOn g D := analyticOnNhd_g.continuousOn

theorem g_injOn : InjOn g D := by
  intro z hz w hw he
  rw [← F_g hz, ← F_g hw, he]

theorem deriv_g_F {w : ℂ} (hw : ‖w‖ < 1) : deriv g (F w) = (deriv F w)⁻¹ := by
  have hFw : F w ∈ D := ⟨w, by simpa using hw, rfl⟩
  have hg := (analyticOnNhd_g _ hFw).differentiableAt.hasDerivAt
  have hf := (hasDerivAt_F hw).differentiableAt.hasDerivAt
  have hc := hg.comp w hf
  have he : g ∘ F =ᶠ[𝓝 w] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hw : w ∈ Metric.ball 0 1)] with z hz
    exact g_F (by simpa using hz)
  have hid := hc.congr_of_eventuallyEq he.symm
  have hm : deriv g (F w) * deriv F w = 1 := hid.unique (hasDerivAt_id w)
  apply mul_right_cancel₀ (deriv_F_ne_zero hw)
  rw [hm, inv_mul_cancel₀ (deriv_F_ne_zero hw)]

theorem deriv_g_ne_zero {z : ℂ} (hz : z ∈ D) : deriv g z ≠ 0 := by
  rw [← F_g hz, deriv_g_F (norm_g_lt hz)]
  exact inv_ne_zero (deriv_F_ne_zero (norm_g_lt hz))

theorem re_g_pos {z : ℂ} (hz : z ∈ D) (hr : 0 < z.re) : 0 < (g z).re := by
  by_contra h
  rcases (le_of_not_gt h).eq_or_lt with he | he
  · have hh := re_F_eq_zero he
    rw [F_g hz] at hh
    linarith
  · have hh := re_F_neg (norm_g_lt hz) he
    rw [F_g hz] at hh
    linarith

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

def T (r : ℝ) : ℝ := (F ((r : ℂ)*I)).im

theorem F_imaginary (r : ℝ) : F ((r : ℂ)*I) = (T r : ℂ)*I := by
  apply Complex.ext <;> simp [T, re_F_imaginary]

@[simp] theorem T_zero : T 0 = 0 := by simp [T]

@[simp] theorem T_neg (r : ℝ) : T (-r) = -T r := by simp [T]

theorem summable_odd_sq : Summable (fun n : ℕ => 1/(2*(n : ℝ)+1)^2) := by
  have h := hasSum_zeta_two.summable.comp_injective (i := fun n : ℕ => 2*n+1)
    (by intro n m h; dsimp at h; omega)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

theorem tsum_odd_sq : (∑' n : ℕ, 1/(2*(n : ℝ)+1)^2) = Real.pi^2/8 := by
  have he : HasSum (fun n : ℕ => 1/((2*n : ℕ) : ℝ)^2) (Real.pi^2/24) := by
    have hh : HasSum (fun n : ℕ => (1/4 : ℝ) * (1/(n : ℝ)^2))
        ((1/4 : ℝ)*(Real.pi^2/6)) := hasSum_zeta_two.mul_left _
    have eqf : (fun n : ℕ => 1/((2*n : ℕ) : ℝ)^2) =
        (fun n : ℕ => (1/4 : ℝ)*(1/(n : ℝ)^2)) := by
      funext n
      push_cast
      simp only [mul_pow, div_mul_eq_div_div]
      norm_num
      ring
    rw [eqf, show Real.pi^2/24 = (1/4 : ℝ)*(Real.pi^2/6) by ring]
    exact hh
  have ho : HasSum (fun n : ℕ => 1/((2*n+1 : ℕ) : ℝ)^2)
      (∑' n : ℕ, 1/(2*(n : ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using summable_odd_sq.hasSum
  have h := (HasSum.even_add_odd (f := fun n : ℕ => 1/(n : ℝ)^2) he ho).unique hasSum_zeta_two
  linarith

@[simp] theorem F_I : F (I : ℂ) = (I : ℂ) := by
  have he : (fun n : ℕ => term n I) = (fun n : ℕ => (I : ℂ) * ((1/(2*(n : ℝ)+1)^2 : ℝ) : ℂ)) := by
    funext n
    have hp : (-1 : ℂ)^n * (I : ℂ)^(2*n+1) = (I : ℂ) := by
      rw [pow_succ, pow_mul, I_sq]
      have h1 : (-1 : ℂ)^n * (-1)^n = 1 := by rw [← mul_pow]; simp
      linear_combination I * h1
    simp only [term, hp, ofReal_div, ofReal_one, ofReal_pow, ofReal_add, ofReal_mul,
      ofReal_ofNat, ofReal_natCast]
    ring
  rw [F, he, tsum_mul_left, ← Complex.ofReal_tsum, tsum_odd_sq]
  push_cast
  field_simp [Real.pi_ne_zero]

@[simp] theorem T_one : T 1 = 1 := by simp [T]

theorem continuousOn_T : ContinuousOn T (Icc (-1) 1) := by
  have hh : ContinuousOn (fun r : ℝ => F ((r : ℂ)*I)) (Icc (-1) 1) := by
    apply continuousOn_F_closedBall.comp (by fun_prop)
    intro r hr
    simpa [Metric.mem_closedBall, norm_mul, norm_real, Real.norm_eq_abs, abs_le] using hr
  exact Complex.continuous_im.comp_continuousOn hh

theorem hasDerivAt_T {r : ℝ} (hr : |r| < 1) :
    HasDerivAt T (deriv F ((r : ℂ)*I)).re r := by
  have hf := (hasDerivAt_F (w := (r : ℂ)*I) (by simpa [norm_mul] using hr)).differentiableAt.hasDerivAt
  have hc := hf.comp (r : ℂ) ((hasDerivAt_id _).mul_const I)
  have hm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hc.comp_ofReal
  convert hm using 1 <;> first | rfl | simp

theorem strictMonoOn_T : StrictMonoOn T (Icc (-1) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) continuousOn_T
  · intro r hr
    have h : |r| < 1 := by simpa only [interior_Icc, mem_Ioo, abs_lt] using hr
    exact (hasDerivAt_T h).hasDerivWithinAt
  · intro r hr
    have h : |r| < 1 := by simpa only [interior_Icc, mem_Ioo, abs_lt] using hr
    exact deriv_F_re_pos (by simpa [norm_mul] using h)

theorem T_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : 0 < T r := by
  have h := strictMonoOn_T (by norm_num : (0 : ℝ) ∈ Icc (-1) 1) ⟨by linarith, hr1⟩ hr
  simpa using h

theorem T_lt_one {r : ℝ} (hr : -1 ≤ r) (hr1 : r < 1) : T r < 1 := by
  have h := strictMonoOn_T ⟨hr, hr1.le⟩ (by norm_num : (1 : ℝ) ∈ Icc (-1) 1) hr1
  simpa using h

theorem exists_T_eq {t : ℝ} (ht : |t| < 1) : ∃ r ∈ Ioo (-1) 1, T r = t := by
  have hh : t ∈ Icc (T (-1)) (T 1) := by simpa using
    ⟨(abs_lt.mp ht).1.le, (abs_lt.mp ht).2.le⟩
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) continuousOn_T hh
  refine ⟨r, ⟨hr.1.lt_of_ne ?_, hr.2.lt_of_ne ?_⟩, he⟩
  · intro h
    rw [← h] at he
    have h' : T (-1) = -1 := by simp
    rw [h'] at he
    linarith [abs_lt.mp ht |>.1]
  · intro h
    rw [h, T_one] at he
    linarith [abs_lt.mp ht |>.2]

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

def A (w : ℂ) : ℝ := (w * deriv F w).re

theorem A_pos {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re) : 0 < A w := by
  rw [A, re_mul_deriv_F hw]
  apply mul_pos (by positivity)
  apply Real.arctan_pos.mpr
  apply div_pos (by linarith)
  nlinarith [norm_nonneg w]

theorem hasDerivAt_horizontal_g {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    HasDerivAt (fun h : ℝ => g ((h : ℂ)+(t : ℂ)*I))
      (deriv g ((v : ℂ)+(t : ℂ)*I)) v := by
  have hg := (analyticOnNhd_g _ hz).differentiableAt.hasDerivAt
  have hc := hg.comp (v : ℂ) ((hasDerivAt_id _).add_const ((t : ℂ)*I))
  convert hc.comp_ofReal using 1 <;> first | rfl | simp only [mul_one]

theorem horizontal_normSq_deriv {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    HasDerivAt (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖^2)
      (2*A (g ((v : ℂ)+(t : ℂ)*I)) / ‖deriv F (g ((v : ℂ)+(t : ℂ)*I))‖^2) v := by
  have hh := (hasDerivAt_horizontal_g hz).norm_sq
  have he : deriv g ((v : ℂ)+(t : ℂ)*I) = (deriv F (g ((v : ℂ)+(t : ℂ)*I)))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hz), F_g hz]
  rw [he] at hh
  convert hh using 1
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  simp only [A, Complex.sq_norm, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.conj_re, Complex.conj_im, RCLike.re_to_complex]
  ring

theorem horizontal_normSq_deriv_pos {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 < v) :
    0 < 2*A (g ((v : ℂ)+(t : ℂ)*I)) / ‖deriv F (g ((v : ℂ)+(t : ℂ)*I))‖^2 := by
  apply div_pos
  · exact mul_pos (by norm_num) (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hv)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (deriv_F_ne_zero (norm_g_lt hz)))

theorem horizontal_segment_mem {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (_hv : 0 ≤ v) {h : ℝ} (hh : h ∈ Icc 0 v) : (h : ℂ)+(t : ℂ)*I ∈ D := by
  let R := ‖g ((v : ℂ)+(t : ℂ)*I)‖
  have hR : R < 1 := norm_g_lt hz
  let C := F '' Metric.closedBall (0 : ℂ) R
  have hCD : C ⊆ D := by
    apply image_mono
    intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using hw
    simpa using hw'.trans_lt hR
  have hCc : IsCompact C := by
    apply (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
    exact continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall hR.le)
  have hCm {a : ℝ} : (a : ℂ)+(t : ℂ)*I ∈ C ↔
      (a : ℂ)+(t : ℂ)*I ∈ D ∧ ‖g ((a : ℂ)+(t : ℂ)*I)‖ ≤ R := by
    constructor
    · rintro ⟨w, hw, he⟩
      have hw' : ‖w‖ ≤ R := by simpa using hw
      refine ⟨hCD ⟨w, hw, he⟩, ?_⟩
      rw [← he, g_F (hw'.trans_lt hR)]
      exact hw'
    · rintro ⟨ha, hr⟩
      exact ⟨g _, by simpa using hr, F_g ha⟩
  let S := Icc h v ∩ (fun a : ℝ => (a : ℂ)+(t : ℂ)*I) ⁻¹' C
  have hSc : IsCompact S := isCompact_Icc.inter_right (hCc.isClosed.preimage (by fun_prop))
  have hvS : v ∈ S := ⟨⟨hh.2, le_rfl⟩, hCm.mpr ⟨hz, le_rfl⟩⟩
  obtain ⟨a, ha, hmin⟩ := hSc.exists_isMinOn ⟨v, hvS⟩ (continuous_id.continuousOn)
  have haD := (hCm.mp ha.2).1
  have haR := (hCm.mp ha.2).2
  have hha : h ≤ a := ha.1.1
  by_cases he : a = h
  · simpa only [he] using haD
  have hha' : h < a := lt_of_le_of_ne hha (Ne.symm he)
  have ha0 : 0 < a := hh.1.trans_lt hha'
  have hopen : IsOpen ((fun b : ℝ => (b : ℂ)+(t : ℂ)*I) ⁻¹' D) :=
    isOpen_D.preimage (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen a haD
  let d := min (a-h) ε / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdh : d < a-h := by dsimp [d]; linarith [min_le_left (a-h) ε]
  have hdε : d < ε := by dsimp [d]; linarith [min_le_right (a-h) ε]
  let b := a-d
  have hhb : h < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b]; linarith
  have hseg : ∀ x ∈ Icc b a, (x : ℂ)+(t : ℂ)*I ∈ D := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hx.2] : x-a ≤ 0)]
    have hxb : a-d ≤ x := hx.1
    linarith
  have hmono : StrictMonoOn (fun x : ℝ => ‖g ((x : ℂ)+(t : ℂ)*I)‖^2) (Icc b a) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc b a)
      (fun x hx => (horizontal_normSq_deriv (hseg x hx)).continuousAt.continuousWithinAt)
      (fun x hx => (horizontal_normSq_deriv (hseg x (interior_subset hx))).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    apply horizontal_normSq_deriv_pos (hseg x hx')
    linarith [hx'.1, hh.1]
  have hnorm : ‖g ((b : ℂ)+(t : ℂ)*I)‖ ≤ R := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    have hm := hmono ⟨le_rfl, hba.le⟩ ⟨hba.le, le_rfl⟩ hba
    have hR0 : 0 ≤ R := norm_nonneg _
    nlinarith [norm_nonneg (g ((a : ℂ)+(t : ℂ)*I))]
  have hbS : b ∈ S := ⟨⟨hhb.le, hba.le.trans ha.1.2⟩,
    hCm.mpr ⟨hseg b ⟨le_rfl, hba.le⟩, hnorm⟩⟩
  have ham : a ≤ b := hmin hbS
  exact False.elim (not_le_of_gt hba ham)

theorem neg_conj_mem_D {z : ℂ} (hz : z ∈ D) : -(starRingEnd ℂ) z ∈ D := by
  rcases hz with ⟨w, hw, rfl⟩
  refine ⟨-(starRingEnd ℂ) w, by simpa using hw, ?_⟩
  simp

theorem g_neg_conj {z : ℂ} (hz : z ∈ D) : g (-(starRingEnd ℂ) z) = -(starRingEnd ℂ) (g z) := by
  apply F_injOn (by simpa using norm_g_lt (neg_conj_mem_D hz))
    (by simpa using norm_g_lt hz)
  rw [F_g (neg_conj_mem_D hz)]
  simp [F_g hz]

theorem conj_mem_D {z : ℂ} (hz : z ∈ D) : (starRingEnd ℂ) z ∈ D := by
  rcases hz with ⟨w, hw, rfl⟩
  exact ⟨(starRingEnd ℂ) w, by simpa using hw, by simp⟩

theorem g_conj {z : ℂ} (hz : z ∈ D) : g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (g z) := by
  apply F_injOn (by simpa using norm_g_lt (conj_mem_D hz))
    (by simpa using norm_g_lt hz)
  simp [F_g (conj_mem_D hz), F_g hz]

theorem horizontal_segment_mem_signed {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    {h : ℝ} (hh : h ∈ uIcc 0 v) : (h : ℂ)+(t : ℂ)*I ∈ D := by
  rcases le_total 0 v with hv | hv
  · rw [uIcc_of_le hv] at hh
    exact horizontal_segment_mem hz hv hh
  · rw [uIcc_of_ge hv] at hh
    have he (a : ℝ) : -((starRingEnd ℂ) ((a : ℂ)+(t : ℂ)*I)) = ((-a : ℝ) : ℂ)+(t : ℂ)*I := by
      apply Complex.ext <;> simp
    have hz' := neg_conj_mem_D hz
    rw [he] at hz'
    have hh' : -h ∈ Icc 0 (-v) := ⟨by linarith [hh.2], by linarith [hh.1]⟩
    have hhD := horizontal_segment_mem hz' (by linarith) hh'
    have hneg := neg_conj_mem_D hhD
    simpa only [he, neg_neg] using hneg

theorem axis_mem_D {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) : (t : ℂ)*I ∈ D := by
  simpa using horizontal_segment_mem_signed hz (left_mem_uIcc (a := 0) (b := v))

theorem g_axis_re_zero {t : ℝ} (ht : (t : ℂ)*I ∈ D) : (g ((t : ℂ)*I)).re = 0 := by
  have he : -(starRingEnd ℂ) ((t : ℂ)*I) = (t : ℂ)*I := by simp
  have hh := g_neg_conj ht
  rw [he] at hh
  have hr := congr_arg Complex.re hh
  simp only [neg_re, conj_re] at hr
  linarith

theorem axis_image {t : ℝ} (ht : (t : ℂ)*I ∈ D) :
    ∃ r ∈ Ioo (-1 : ℝ) 1, g ((t : ℂ)*I) = (r : ℂ)*I ∧ T r = t := by
  let r := (g ((t : ℂ)*I)).im
  have he : g ((t : ℂ)*I) = (r : ℂ)*I := by
    apply Complex.ext <;> simp [r, g_axis_re_zero ht]
  have hr : |r| < 1 := by
    have hh := norm_g_lt ht
    rw [he] at hh
    simpa [norm_mul] using hh
  refine ⟨r, abs_lt.mp hr, he, ?_⟩
  have hh := congr_arg Complex.im (F_g ht)
  rw [he] at hh
  simpa [T] using hh

theorem im_mem_Ioo {z : ℂ} (hz : z ∈ D) : z.im ∈ Ioo (-1 : ℝ) 1 := by
  have hz' : (z.re : ℂ)+(z.im : ℂ)*I ∈ D := by simpa using hz
  obtain ⟨r, hr, _, ht⟩ := axis_image (axis_mem_D hz')
  rw [← ht]
  refine ⟨?_, T_lt_one hr.1.le hr.2⟩
  have h := strictMonoOn_T (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1) ⟨hr.1.le, hr.2.le⟩ hr.1
  simpa using h

theorem imaginary_mem_D {t : ℝ} (ht : |t| < 1) : (t : ℂ)*I ∈ D := by
  obtain ⟨r, hr, he⟩ := exists_T_eq ht
  exact ⟨(r : ℂ)*I, by simpa [Metric.mem_ball, norm_mul, abs_lt] using hr,
    by rw [F_imaginary r, he]⟩

theorem horizontal_radius_strictMono {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 ≤ v) : StrictMonoOn (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖) (Icc 0 v) := by
  have hm : StrictMonoOn (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖^2) (Icc 0 v) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 v)
      (fun h hh => (horizontal_normSq_deriv (horizontal_segment_mem hz hv hh)).continuousAt.continuousWithinAt)
      (fun h hh => (horizontal_normSq_deriv (horizontal_segment_mem hz hv (interior_subset hh))).hasDerivWithinAt)
    intro h hh
    apply horizontal_normSq_deriv_pos (horizontal_segment_mem hz hv (interior_subset hh))
    have hh' : h ∈ Ioo 0 v := by simpa only [interior_Icc] using hh
    exact hh'.1
  intro a ha b hb hab
  have hh := hm ha hb hab
  nlinarith [norm_nonneg (g ((a : ℂ)+(t : ℂ)*I)), norm_nonneg (g ((b : ℂ)+(t : ℂ)*I))]

theorem T_norm_g_axis {t : ℝ} (ht : (t : ℂ)*I ∈ D) : T ‖g ((t : ℂ)*I)‖ = |t| := by
  obtain ⟨r, hr, he, hT⟩ := axis_image ht
  rw [he]
  simp only [norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]
  rcases le_total 0 r with hr0 | hr0
  · rw [abs_of_nonneg hr0, ← hT, abs_of_nonneg]
    have h := strictMonoOn_T.monotoneOn (by norm_num : (0 : ℝ) ∈ Icc (-1) 1)
      ⟨hr.1.le, hr.2.le⟩ hr0
    simpa using h
  · rw [abs_of_nonpos hr0, T_neg, ← hT, abs_of_nonpos]
    have h := strictMonoOn_T.monotoneOn ⟨hr.1.le, hr.2.le⟩
      (by norm_num : (0 : ℝ) ∈ Icc (-1) 1) hr0
    simpa using h

theorem vertical_gap_pos {z : ℂ} (hz : z ∈ D) (hr : 0 < z.re) :
    0 < T ‖g z‖ - |z.im| := by
  have hz' : (z.re : ℂ)+(z.im : ℂ)*I ∈ D := by simpa using hz
  have hnorm := horizontal_radius_strictMono hz' hr.le
    (left_mem_Icc.mpr hr.le) (right_mem_Icc.mpr hr.le) hr
  simp only [ofReal_zero, zero_add, re_add_im] at hnorm
  rw [← T_norm_g_axis (axis_mem_D hz')]
  have hh := strictMonoOn_T
    ⟨by linarith [norm_nonneg (g ((z.im : ℂ)*I))], (norm_g_lt (axis_mem_D hz')).le⟩
    ⟨by linarith [norm_nonneg (g z)], (norm_g_lt hz).le⟩ hnorm
  linarith

end
end PlanarLens

end LowerBoundInline

end OAI
