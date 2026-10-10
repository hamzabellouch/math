import OAI.Probability.SLE.Geometry.MarkedRoutes

namespace OAI

/-! Fixed positive clearance of both marked-point routes from the past
and from the complete polygonal hook, away from their common initial point. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

lemma markedHook_re_bounds {w : ℂ} {R a t : ℝ} (hR : w.re < R)
    (hw : w.im < 2) (ha : 0 < a) (ht : 0 ≤ t) :
    w.re - a ≤ (markedHook w R 2 a t).re ∧ (markedHook w R 2 a t).re ≤ R := by
  rcases markedHook_pieces w hR hw ha ht with ⟨ht, he⟩ | ⟨ht, he⟩ |
    ⟨ht, he⟩ | ⟨ht, he⟩
  all_goals
    rw [he]
    simp only [hookTop, hookDown, hookLeft, hookUp, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero]
    try simp only [mem_Icc] at ht
    constructor <;> linarith

lemma markedHook_im_lower {w : ℂ} {R a t : ℝ} (hR : w.re < R)
    (hw : w.im < 2) (ha : 0 < a) (ht : 0 ≤ t) :
    w.im ≤ (markedHook w R 2 a t).im := by
  rcases markedHook_pieces w hR hw ha ht with ⟨ht, he⟩ | ⟨ht, he⟩ |
    ⟨ht, he⟩ | ⟨ht, he⟩
  all_goals
    rw [he]
    simp only [hookTop, hookDown, hookLeft, hookUp, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add]
    try simp only [mem_Icc] at ht
    linarith

lemma markedLeftRoute_before_two {w : ℂ} {a t : ℝ} (ha : 0 ≤ a) (hw : -3 ≤ w.re) (ht : t ≤ 2) :
    (markedLeftRoute w a t).re ≤ w.re ∧
      w.im - a ≤ (markedLeftRoute w a t).im := by
  rw [markedLeftRoute_re, markedLeftRoute_im,
    unitClip_of_nonpos (by linarith : t - 2 ≤ 0), mul_zero, add_zero]
  have hc1 := unitClip_le_one t
  constructor
  · have h := unitClip_nonneg (t - 1)
    nlinarith
  · nlinarith

lemma markedLeftRoute_after_two (w : ℂ) (a : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    (markedLeftRoute w a t).re = -3 := by
  rw [markedLeftRoute_re, unitClip_of_one_le (by linarith : 1 ≤ t - 1)]
  ring

lemma markedRightRoute_before_two {w : ℂ} {a t : ℝ}
    (hw : w.im ≤ 1) (ha : 0 ≤ a) (ht : t ≤ 2) :
    (markedRightRoute w a t).re ≤ w.re ∧ w.im ≤ (markedRightRoute w a t).im := by
  rw [markedRightRoute_re, markedRightRoute_im,
    unitClip_of_nonpos (by linarith : t - 2 ≤ 0),
    unitClip_of_nonpos (by linarith : t - 3 ≤ 0)]
  have h0 := unitClip_nonneg t
  have h1 := unitClip_nonneg (t - 1)
  constructor <;> nlinarith

lemma markedRightRoute_middle {w : ℂ} {a t : ℝ}
    (hw : w.re ≤ 1) (ha : 0 ≤ a) (ht : t ∈ Icc (2 : ℝ) 3) :
    w.re - a / 2 ≤ (markedRightRoute w a t).re ∧
      (markedRightRoute w a t).im = 2 + a := by
  rw [markedRightRoute_re, markedRightRoute_im,
    unitClip_of_one_le (by linarith [ht.1] : 1 ≤ t),
    unitClip_of_one_le (by linarith [ht.1] : 1 ≤ t - 1),
    unitClip_of_nonpos (by linarith [ht.2] : t - 3 ≤ 0)]
  have h := unitClip_nonneg (t - 2)
  constructor <;> nlinarith

lemma markedRightRoute_after_three (w : ℂ) (a : ℝ) {t : ℝ} (ht : 3 ≤ t) :
    (markedRightRoute w a t).re = 3 := by
  rw [markedRightRoute_re, unitClip_of_one_le (by linarith : 1 ≤ t),
    unitClip_of_one_le (by linarith : 1 ≤ t - 2)]
  ring

/-- The explicit routes are uniformly separated from every admissible
past point, including before the local departure from the marked point. -/
theorem markedRoutes_past_clearance {w q : ℂ} {a t : ℝ}
    (hwr : -3 ≤ w.re) (hwr1 : w.re ≤ 1) (hwi1 : w.im ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hqre : -2 ≤ q.re ∧ q.re ≤ 2) (hqim : q.im ≤ 2)
    (hq : q.im ≤ w.im - 2 * a ∨ w.re + 2 * a ≤ q.re) :
    a ≤ dist (markedLeftRoute w a t) q ∧ a ≤ dist (markedRightRoute w a t) q := by
  have hlr := Complex.abs_re_le_norm (markedLeftRoute w a t - q)
  have hli := Complex.abs_im_le_norm (markedLeftRoute w a t - q)
  have hrr := Complex.abs_re_le_norm (markedRightRoute w a t - q)
  have hri := Complex.abs_im_le_norm (markedRightRoute w a t - q)
  simp only [Complex.sub_re, Complex.sub_im, ← dist_eq_norm] at hlr hli hrr hri
  constructor
  · by_cases ht : t ≤ 2
    · have hb := markedLeftRoute_before_two ha hwr ht
      rcases hq with hq | hq
      · linarith [le_abs_self ((markedLeftRoute w a t).im - q.im)]
      · linarith [neg_le_abs ((markedLeftRoute w a t).re - q.re)]
    · rw [markedLeftRoute_after_two w a (le_of_not_ge ht)] at hlr
      linarith [neg_le_abs (-3 - q.re), hqre.1]
  · by_cases ht : t ≤ 2
    · have hb := markedRightRoute_before_two hwi1 ha ht
      rcases hq with hq | hq
      · linarith [le_abs_self ((markedRightRoute w a t).im - q.im)]
      · linarith [neg_le_abs ((markedRightRoute w a t).re - q.re)]
    · by_cases ht3 : t ≤ 3
      · have hb := markedRightRoute_middle hwr1 ha ⟨le_of_not_ge ht, ht3⟩
        rw [hb.2] at hri
        linarith [le_abs_self (2 + a - q.im)]
      · rw [markedRightRoute_after_three w a (le_of_not_ge ht3)] at hrr
        linarith [le_abs_self (3 - q.re), hqre.2]

lemma markedLeftRoute_early_below {w : ℂ} {a t : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Icc (1 / 4 : ℝ) 2) :
    (markedLeftRoute w a t).im ≤ w.im - a / 4 := by
  rw [markedLeftRoute_im, unitClip_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0)]
  have hc : 1 / 4 ≤ unitClip t :=
    (show 1 / 4 ≤ min 1 t from le_min (by norm_num) ht.1).trans (le_max_right _ _)
  nlinarith

/-- The lower route avoids the complete hook after time 1/4. -/
theorem markedLeftRoute_hook_clearance {w : ℂ} {R a t u : ℝ}
    (hwr : 0 ≤ w.re) (hwi : w.im < 2) (hR : w.re < R)
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 / 4 ≤ t) (hu : 0 ≤ u) :
    a / 4 ≤ dist (markedLeftRoute w a t) (markedHook w R 2 a u) := by
  have hr := Complex.abs_re_le_norm (markedLeftRoute w a t - markedHook w R 2 a u)
  have hi := Complex.abs_im_le_norm (markedLeftRoute w a t - markedHook w R 2 a u)
  simp only [Complex.sub_re, Complex.sub_im, ← dist_eq_norm] at hr hi
  by_cases ht2 : t ≤ 2
  · have h := markedLeftRoute_early_below (w := w) ha.le ⟨ht, ht2⟩
    have h' := markedHook_im_lower hR hwi ha hu
    linarith [neg_le_abs ((markedLeftRoute w a t).im - (markedHook w R 2 a u).im)]
  · rw [markedLeftRoute_after_two w a (le_of_not_ge ht2)] at hr
    have h := (markedHook_re_bounds hR hwi ha hu).1
    linarith [neg_le_abs (-3 - (markedHook w R 2 a u).re)]

lemma markedRightRoute_first {w : ℂ} {a t : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Icc (1 / 4 : ℝ) 1) :
    w.re - a / 2 ≤ (markedRightRoute w a t).re ∧
    (markedRightRoute w a t).re ≤ w.re - a / 8 ∧
    w.im + a / 8 ≤ (markedRightRoute w a t).im ∧
    (markedRightRoute w a t).im ≤ w.im + a / 2 := by
  rw [markedRightRoute_re, markedRightRoute_im, unitClip_of_mem ⟨by linarith [ht.1], ht.2⟩,
    unitClip_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0),
    unitClip_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0),
    unitClip_of_nonpos (by linarith [ht.2] : t - 3 ≤ 0)]
  constructor
  · nlinarith [ht.2]
  constructor
  · nlinarith [ht.1]
  constructor <;> nlinarith [ht.1, ht.2]

lemma markedRightRoute_second {w : ℂ} {a t : ℝ} (hw : w.im ≤ 1) (ha : 0 ≤ a)
    (ht : t ∈ Icc (1 : ℝ) 2) :
    (markedRightRoute w a t).re = w.re - a / 2 ∧
    w.im + a / 2 ≤ (markedRightRoute w a t).im := by
  rw [markedRightRoute_re, markedRightRoute_im, unitClip_of_one_le ht.1,
    unitClip_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0),
    unitClip_of_nonpos (by linarith [ht.2] : t - 3 ≤ 0)]
  have h := unitClip_nonneg (t - 1)
  constructor
  · ring
  · nlinarith

/-- The upper route runs in the gap between the two vertical legs,
then above the horizontal top, and finally along the exterior line. -/
theorem markedRightRoute_hook_clearance {w : ℂ} {R a t u : ℝ}
    (hwr1 : w.re ≤ 1) (hwi : w.im ≤ 1) (hR : w.re < R) (hR2 : R ≤ 2)
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 / 4 ≤ t) (hu : 0 ≤ u) :
    a / 8 ≤ dist (markedRightRoute w a t) (markedHook w R 2 a u) := by
  have hr := Complex.abs_re_le_norm (markedRightRoute w a t - markedHook w R 2 a u)
  have hi := Complex.abs_im_le_norm (markedRightRoute w a t - markedHook w R 2 a u)
  simp only [Complex.sub_re, Complex.sub_im, ← dist_eq_norm] at hr hi
  have hrp := le_abs_self ((markedRightRoute w a t).re - (markedHook w R 2 a u).re)
  have hrn := neg_le_abs ((markedRightRoute w a t).re - (markedHook w R 2 a u).re)
  have hip := le_abs_self ((markedRightRoute w a t).im - (markedHook w R 2 a u).im)
  have hin := neg_le_abs ((markedRightRoute w a t).im - (markedHook w R 2 a u).im)
  by_cases ht3 : 3 ≤ t
  · have hq := (markedHook_re_bounds hR (by linarith) ha hu).2
    rw [markedRightRoute_after_three w a ht3] at hr hrp
    linarith
  have hwi2 : w.im < 2 := by linarith
  by_cases ht1 : t ≤ 1
  · obtain ⟨hx0, hx1, hy0, hy1⟩ := markedRightRoute_first (w := w) ha.le ⟨ht, ht1⟩
    rcases markedHook_pieces w hR hwi2 ha hu with ⟨hq, he⟩ | ⟨hq, he⟩ |
      ⟨hq, he⟩ | ⟨hq, he⟩
    all_goals
      rw [he] at hr hi hrp hrn hip hin ⊢
      simp only [hookTop, hookDown, hookLeft, hookUp, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
        at hr hi hrp hrn hip hin ⊢
      try simp only [mem_Icc] at hq
      linarith
  · by_cases ht2 : t ≤ 2
    · obtain ⟨hx, hy⟩ := markedRightRoute_second hwi ha.le ⟨le_of_not_ge ht1, ht2⟩
      rcases markedHook_pieces w hR hwi2 ha hu with ⟨hq, he⟩ | ⟨hq, he⟩ |
        ⟨hq, he⟩ | ⟨hq, he⟩
      all_goals
        rw [he] at hr hi hrp hrn hip hin ⊢
        simp only [hookTop, hookDown, hookLeft, hookUp, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
          at hr hi hrp hrn hip hin ⊢
        try simp only [mem_Icc] at hq
        linarith
    · obtain ⟨hx, hy⟩ := markedRightRoute_middle hwr1 ha.le ⟨le_of_not_ge ht2, le_of_not_ge ht3⟩
      rcases markedHook_pieces w hR hwi2 ha hu with ⟨hq, he⟩ | ⟨hq, he⟩ |
        ⟨hq, he⟩ | ⟨hq, he⟩
      all_goals
        rw [he] at hr hi hrp hrn hip hin ⊢
        simp only [hookTop, hookDown, hookLeft, hookUp, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
          at hr hi hrp hrn hip hin ⊢
        try simp only [mem_Icc] at hq
        linarith

end SLEExactGauge.Serpentine

end

end OAI
