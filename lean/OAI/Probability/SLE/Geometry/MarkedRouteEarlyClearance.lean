import OAI.Probability.SLE.Geometry.MarkedRouteClearance

namespace OAI

/-! Uniform hook separation already at the early local-side test time. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

private lemma right_early_box {w : ℂ} {a t : ℝ} (ha : 0 ≤ a)
    (ht : t ∈ Icc (1 / 64 : ℝ) (1 / 4)) :
    w.re - a / 8 ≤ (markedRightRoute w a t).re ∧
    (markedRightRoute w a t).re ≤ w.re - a / 128 ∧
    w.im + a / 128 ≤ (markedRightRoute w a t).im ∧
    (markedRightRoute w a t).im ≤ w.im + a / 8 := by
  rw [markedRightRoute_re, markedRightRoute_im,
    unitClip_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    unitClip_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0),
    unitClip_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0),
    unitClip_of_nonpos (by linarith [ht.2] : t - 3 ≤ 0)]
  constructor
  · nlinarith [ht.2]
  constructor
  · nlinarith [ht.1]
  constructor <;> nlinarith [ht.1, ht.2]

private lemma left_very_early_clearance {w : ℂ} {R a t u : ℝ}
    (hwi : w.im < 2) (hR : w.re < R) (ha : 0 < a)
    (ht : t ∈ Icc (1 / 64 : ℝ) (1 / 4)) (hu : 0 ≤ u) :
    a / 512 ≤ dist (markedLeftRoute w a t) (markedHook w R 2 a u) := by
  have hbelow : (markedLeftRoute w a t).im ≤ w.im - a / 64 := by
    rw [markedLeftRoute_im, unitClip_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      unitClip_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0)]
    nlinarith [ht.1]
  have hq := markedHook_im_lower hR hwi ha hu
  have hi := Complex.abs_im_le_norm (markedLeftRoute w a t - markedHook w R 2 a u)
  rw [Complex.sub_im, ← dist_eq_norm] at hi
  linarith [neg_le_abs ((markedLeftRoute w a t).im - (markedHook w R 2 a u).im)]

private lemma right_very_early_clearance {w : ℂ} {R a t u : ℝ}
    (hwi : w.im ≤ 1) (hR : w.re < R) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : t ∈ Icc (1 / 64 : ℝ) (1 / 4)) (hu : 0 ≤ u) :
    a / 512 ≤ dist (markedRightRoute w a t) (markedHook w R 2 a u) := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := right_early_box (w := w) ha.le ht
  have hr := Complex.abs_re_le_norm (markedRightRoute w a t - markedHook w R 2 a u)
  have hi := Complex.abs_im_le_norm (markedRightRoute w a t - markedHook w R 2 a u)
  simp only [Complex.sub_re, Complex.sub_im, ← dist_eq_norm] at hr hi
  have hrp := le_abs_self ((markedRightRoute w a t).re - (markedHook w R 2 a u).re)
  have hrn := neg_le_abs ((markedRightRoute w a t).re - (markedHook w R 2 a u).re)
  have hip := le_abs_self ((markedRightRoute w a t).im - (markedHook w R 2 a u).im)
  have hin := neg_le_abs ((markedRightRoute w a t).im - (markedHook w R 2 a u).im)
  rcases markedHook_pieces w hR (show w.im < 2 by linarith) ha hu with ⟨hq, he⟩ | ⟨hq, he⟩ |
      ⟨hq, he⟩ | ⟨hq, he⟩
  all_goals
    rw [he] at hr hi hrp hrn hip hin ⊢
    simp only [hookTop, hookDown, hookLeft, hookUp, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
      at hr hi hrp hrn hip hin ⊢
    try simp only [mem_Icc] at hq
    linarith

/-- A common margin for both routes from the local-side test onward. -/
theorem markedRoutes_hook_clearance_early {w : ℂ} {R a t u : ℝ}
    (hwr : 0 ≤ w.re) (hwr1 : w.re ≤ 1) (hwi : w.im ≤ 1)
    (hR : w.re < R) (hR2 : R ≤ 2) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 1 / 64 ≤ t) (hu : 0 ≤ u) :
    a / 512 ≤ dist (markedLeftRoute w a t) (markedHook w R 2 a u) ∧
    a / 512 ≤ dist (markedRightRoute w a t) (markedHook w R 2 a u) := by
  by_cases ht' : 1 / 4 ≤ t
  · constructor
    · exact (by linarith : a / 512 ≤ a / 4).trans
        (markedLeftRoute_hook_clearance hwr (by linarith) hR ha ha1 ht' hu)
    · exact (by linarith : a / 512 ≤ a / 8).trans
        (markedRightRoute_hook_clearance hwr1 hwi hR hR2 ha ha1 ht' hu)
  · exact ⟨left_very_early_clearance (by linarith) hR ha ⟨ht, le_of_not_ge ht'⟩ hu,
      right_very_early_clearance hwi hR ha ha1 ⟨ht, le_of_not_ge ht'⟩ hu⟩

end SLEExactGauge.Serpentine

end

end OAI
