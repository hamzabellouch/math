import OAI.Probability.SLE.Geometry.MarkedRouteSides
import OAI.Probability.SLE.Geometry.LocalCrosscutSides

namespace OAI

/-! Uniform small physical tube neighbourhoods depart on opposite local
sides of the marked corner. Openness determines either orientation of the
actual conformal map-out; no boundary-order assertion is assumed. -/

noncomputable section
open Set Metric
open scoped Topology

namespace SLEExactGauge.Serpentine
open RibbonCoordinates CrosscutSides

lemma markedLeftRoute_small_time (w : ℂ) (a : ℝ) :
    markedLeftRoute w a (1 / 48) = w - (a / 48 : ℝ) * Complex.I := by
  apply Complex.ext <;> norm_num [unitClip]; ring

lemma markedRightRoute_small_time (w : ℂ) (a : ℝ) :
    markedRightRoute w a (1 / 48) =
      w + ((-a / 96 : ℝ) : ℂ) + (a / 96 : ℝ) * Complex.I := by
  apply Complex.ext <;> norm_num [unitClip] <;> ring

lemma marked_small_route_dist (w : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    dist (markedLeftRoute w a (1 / 48)) w ≤ a / 48 ∧
      dist (markedRightRoute w a (1 / 48)) w ≤ a / 48 := by
  constructor
  · rw [markedLeftRoute_small_time, dist_eq_norm, sub_sub_cancel_left,
      norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_nonneg (by positivity : 0 ≤ a / 48)]
  · rw [markedRightRoute_small_time, dist_eq_norm]
    have he : w + ((-a / 96 : ℝ) : ℂ) + (a / 96 : ℝ) * Complex.I - w =
        ((-a / 96 : ℝ) : ℂ) + (a / 96 : ℝ) * Complex.I := by ring
    rw [he]
    calc
      _ ≤ |(-a / 96 : ℝ)| + |a / 96| := by
        simpa using Complex.norm_le_abs_re_add_abs_im
          (((-a / 96 : ℝ) : ℂ) + (a / 96 : ℝ) * Complex.I)
      _ = a / 48 := by rw [abs_of_nonpos (by linarith), abs_of_nonneg (by positivity)]; ring

lemma marked_small_tube_coordinate {w y : ℂ} {a : ℝ} (ha : 0 < a)
    (hnear : dist y (markedLeftRoute w a (1 / 48)) < a / 10000 ∨
      dist y (markedRightRoute w a (1 / 48)) < a / 10000) :
    (markedCornerChart w).symm y ∈ ball (0 : ℂ) (a / 12) := by
  have hd : dist y w < a / 10000 + a / 48 := by
    rcases hnear with hn | hn
    · exact (dist_triangle y _ w).trans_lt (add_lt_add_of_lt_of_le hn (marked_small_route_dist w ha.le).1)
    · exact (dist_triangle y _ w).trans_lt (add_lt_add_of_lt_of_le hn (marked_small_route_dist w ha.le).2)
  have hb := markedCornerChart_norm_lower w ((markedCornerChart w).symm y)
  rw [Homeomorph.apply_symm_apply] at hb
  rw [mem_ball, dist_zero_right]
  linarith

lemma marked_small_tube_positive {w y : ℂ} {a : ℝ} (ha : 0 < a)
    (hn : dist y (markedLeftRoute w a (1 / 48)) < a / 10000) :
    0 < ((markedCornerChart w).symm y).im := by
  have hi := (Complex.abs_im_le_norm (y - markedLeftRoute w a (1 / 48))).trans_lt
    (show ‖y - markedLeftRoute w a (1 / 48)‖ < a / 10000 by simpa only [dist_eq_norm] using hn)
  rw [Complex.sub_im, markedLeftRoute_small_time] at hi
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero] at hi
  rw [markedCornerChart_symm_im]
  exact lt_of_lt_of_le (by linarith [(abs_lt.mp hi).2] : 0 < w.im - y.im) (le_max_right _ _)

lemma marked_small_tube_negative {w y : ℂ} {a : ℝ} (ha : 0 < a)
    (hn : dist y (markedRightRoute w a (1 / 48)) < a / 10000) :
    ((markedCornerChart w).symm y).im < 0 := by
  have hd : ‖y - markedRightRoute w a (1 / 48)‖ < a / 10000 := by simpa only [dist_eq_norm] using hn
  have hi := (Complex.abs_im_le_norm _).trans_lt hd
  have hr := (Complex.abs_re_le_norm _).trans_lt hd
  rw [Complex.sub_im, markedRightRoute_small_time] at hi
  rw [Complex.sub_re, markedRightRoute_small_time] at hr
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero] at hi
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero] at hr
  rw [markedCornerChart_symm_im, max_lt_iff]
  constructor <;> linarith [(abs_lt.mp hi).1, (abs_lt.mp hr).2]

theorem marked_physical_tubes_opposite_sides
    (hopen : PublishedPlanarDiskOpenness) (w : ℂ) {a : ℝ} (ha : 0 < a)
    (f : ℂ → ℂ) (j : ℂ → ℝ)
    (hf : ContinuousOn f (ball (0 : ℂ) (a / 12)))
    (hfi : InjOn f (ball (0 : ℂ) (a / 12)))
    (hzero : ∀ z ∈ ball (0 : ℂ) (a / 12), (f z).re = 0 ↔ z.im = 0)
    (hrel : ∀ z ∈ ball (0 : ℂ) (a / 12), j (markedCornerChart w z) = (f z).re) :
    ((∀ y : ℂ, dist y (markedLeftRoute w a (1 / 48)) < a / 10000 → 0 < j y) ∧
      (∀ y : ℂ, dist y (markedRightRoute w a (1 / 48)) < a / 10000 → j y < 0)) ∨
    ((∀ y : ℂ, dist y (markedLeftRoute w a (1 / 48)) < a / 10000 → j y < 0) ∧
      (∀ y : ℂ, dist y (markedRightRoute w a (1 / 48)) < a / 10000 → 0 < j y)) := by
  have ha12 : 0 < a / 12 := by positivity
  have hz := (hzero 0 (mem_ball_self ha12)).mpr (by simp)
  obtain h | h := opposite_half_disk_signs f 0 ha12 hf (hopen f 0 _ ha12 hf hfi) hz hzero
  · left
    constructor
    · intro y hy
      have hb := marked_small_tube_coordinate ha (Or.inl hy)
      have he := hrel _ hb
      rw [Homeomorph.apply_symm_apply] at he
      rw [he]
      exact h.1 _ hb (marked_small_tube_positive ha hy)
    · intro y hy
      have hb := marked_small_tube_coordinate ha (Or.inr hy)
      have he := hrel _ hb
      rw [Homeomorph.apply_symm_apply] at he
      rw [he]
      exact h.2 _ hb (marked_small_tube_negative ha hy)
  · right
    constructor
    · intro y hy
      have hb := marked_small_tube_coordinate ha (Or.inl hy)
      have he := hrel _ hb
      rw [Homeomorph.apply_symm_apply] at he
      rw [he]
      exact h.1 _ hb (marked_small_tube_positive ha hy)
    · intro y hy
      have hb := marked_small_tube_coordinate ha (Or.inr hy)
      have he := hrel _ hb
      rw [Homeomorph.apply_symm_apply] at he
      rw [he]
      exact h.2 _ hb (marked_small_tube_negative ha hy)

end SLEExactGauge.Serpentine

end

end OAI
