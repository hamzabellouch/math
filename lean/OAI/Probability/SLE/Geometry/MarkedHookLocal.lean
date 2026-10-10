import OAI.Probability.SLE.Geometry.MarkedCornerBounds

namespace OAI

/-! The complete marked hook has exactly its two adjacent legs in a
small corner-chart neighbourhood. A separated preceding guide contributes
no other local intersection. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma markedCornerChart_real_iff (w z : ℂ) :
    ((markedCornerChart w z).re = w.re ∧ w.im ≤ (markedCornerChart w z).im) ∨
      ((markedCornerChart w z).im = w.im ∧ (markedCornerChart w z).re ≤ w.re) ↔
    z.im = 0 := by
  rw [← markedCornerChart_real_image]
  constructor
  · rintro ⟨u, hu⟩
    have h := (markedCornerChart w).injective hu
    simpa only [Complex.ofReal_im] using congrArg Complex.im h.symm
  · intro hz
    refine ⟨z.re, ?_⟩
    congr 1
    apply Complex.ext <;> simp [hz]

lemma markedHook_in_small_corner {w z : ℂ} {R H a δ t : ℝ}
    (hR : w.re < R) (hH : w.im < H) (ha : 0 < a)
    (hδH : 3 * δ < H - w.im) (hδa : 3 * δ < a)
    (hz : ‖z‖ < δ) (ht : 0 ≤ t)
    (he : markedHook w R H a t = markedCornerChart w z) : z.im = 0 := by
  have hd : dist (markedCornerChart w z) w < 3 * δ :=
    (markedCornerChart_norm w z).trans_lt (by linarith)
  have hy := Complex.abs_im_le_norm (markedCornerChart w z - w)
  have hx := Complex.abs_re_le_norm (markedCornerChart w z - w)
  rw [Complex.sub_im] at hy
  rw [Complex.sub_re] at hx
  rw [← dist_eq_norm] at hy hx
  apply (markedCornerChart_real_iff w z).mp
  rcases markedHook_pieces w hR hH ha ht with ⟨_, hh⟩ | ⟨ht, hh⟩ |
      ⟨ht, hh⟩ | ⟨_, hh⟩
  · have him : (markedCornerChart w z).im = H := by
      rw [← he, hh]
      simp [hookTop]
    rw [him] at hy
    linarith [le_abs_self (H - w.im)]
  · left
    rw [← he, hh]
    simp only [hookDown, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add]
    exact ⟨trivial, by linarith [ht.2]⟩
  · right
    rw [← he, hh]
    simp only [hookLeft, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add]
    exact ⟨trivial, by linarith [ht.1]⟩
  · have hre : (markedCornerChart w z).re = w.re - a := by
      rw [← he, hh]
      simp [hookUp]
    rw [hre] at hx
    linarith [neg_le_abs (w.re - a - w.re)]

lemma markedHook_contains_small_real {w z : ℂ} {R H a δ : ℝ}
    (hR : w.re < R) (hδH : δ < H - w.im) (hδa : δ < a)
    (hz : ‖z‖ < δ) (him : z.im = 0) :
    ∃ t : ℝ, 0 ≤ t ∧ markedHook w R H a t = markedCornerChart w z := by
  have hu : |z.re| < δ := (Complex.abs_re_le_norm z).trans_lt hz
  have hez : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  rw [hez]
  by_cases hp : 0 < z.re
  · refine ⟨(R - w.re) + (H - w.im) + z.re, ?_, ?_⟩
    · linarith [le_abs_self z.re, neg_le_abs z.re]
    · rw [markedHook, curveJoin_of_gt (by linarith [neg_le_abs z.re]),
        curveJoin_of_gt (by linarith), curveJoin_of_le (by linarith [le_abs_self z.re]),
        markedCornerChart_real_nonneg w hp.le]
      apply Complex.ext <;> simp [hookLeft]
  · have hn : z.re ≤ 0 := le_of_not_gt hp
    refine ⟨(R - w.re) + (H - w.im) + z.re, ?_, ?_⟩
    · linarith [neg_le_abs z.re]
    · rw [markedHook, curveJoin_of_gt (by linarith [neg_le_abs z.re]),
        curveJoin_of_le (by linarith), markedCornerChart_real_nonpos w hn]
      apply Complex.ext <;> simp [hookDown]; ring

/-- The local intersection statement needed to straighten the complete guide. -/
theorem markedHook_small_corner_iff {w z : ℂ} {R H a δ : ℝ}
    (hR : w.re < R) (hH : w.im < H) (ha : 0 < a) (hδ : 0 < δ)
    (hδH : 3 * δ < H - w.im) (hδa : 3 * δ < a) (hz : ‖z‖ < δ) :
    (∃ t : ℝ, 0 ≤ t ∧ markedHook w R H a t = markedCornerChart w z) ↔ z.im = 0 := by
  constructor
  · rintro ⟨t, ht, he⟩
    exact markedHook_in_small_corner hR hH ha hδH hδa hz ht he
  · exact markedHook_contains_small_real hR (by linarith) (by linarith) hz

lemma separated_prefix_outside_corner {w z p : ℂ} {δ d : ℝ}
    (hd : d ≤ dist p w) (hδ : 3 * δ < d) (hz : ‖z‖ < δ) :
    p ≠ markedCornerChart w z := by
  intro he
  have hb := markedCornerChart_norm w z
  rw [← he] at hb
  linarith

end SLEExactGauge.Serpentine

end

end OAI
