import OAI.Probability.SLE.Gauge.RibbonMiddleMass
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace OAI

/-! Explicit columns and circular turns for the dense-visit serpentine.
The array and its normal bands fit in the displaced disk and stay a fixed
distance from the marked point. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine

def side (j : ℕ) : ℝ := if Even j then 1 else -1

lemma side_abs (j : ℕ) : |side j| = 1 := by
  unfold side
  split <;> norm_num

lemma side_sq (j : ℕ) : side j ^ 2 = 1 := by
  unfold side
  split <;> norm_num

def displacementSign (w : ℂ) : ℝ := if 0 ≤ w.re then 1 else -1

def center (s : ℝ) (w : ℂ) : ℂ := w + ((displacementSign w * (s / 4) : ℝ) : ℂ)

def halfHeight (s : ℝ) : ℝ := s / 200

def spacing (h : ℝ) (m : ℕ) : ℝ := h / m

def turnRadius (h : ℝ) (m : ℕ) : ℝ := h / (2 * m)

def ribbonWidth (h : ℝ) (m : ℕ) : ℝ := h / (100 * m)

def columnOffset (h : ℝ) (m j : ℕ) : ℝ := -h + j * spacing h m

/-- The closed width-one band over one straight pass, in physical scale. -/
def columnPoint (c : ℂ) (h : ℝ) (m j : ℕ) (y a : ℝ) : ℂ :=
  c + ((columnOffset h m j - side j * ribbonWidth h m * a : ℝ) : ℂ) +
    (y : ℂ) * Complex.I

/-- A circular connector, with its actual normal ribbon coordinate `a`.
The parameter runs from zero to pi, alternating above and below. -/
def turnPoint (c : ℂ) (h : ℝ) (m j : ℕ) (t a : ℝ) : ℂ :=
  c + ((columnOffset h m j + turnRadius h m : ℝ) : ℂ) +
    (side j * h : ℂ) * Complex.I +
    ((turnRadius h m + side j * ribbonWidth h m * a : ℝ) : ℂ) *
      ((-Real.cos t : ℝ) + (side j * Real.sin t : ℂ) * Complex.I)

lemma center_dist {s : ℝ} (hs : 0 ≤ s) (w : ℂ) : dist (center s w) w = s / 4 := by
  rw [center, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (div_nonneg hs (by norm_num))]
  have hh : |displacementSign w| = 1 := by unfold displacementSign; split <;> norm_num
  rw [hh, one_mul]

lemma center_im (s : ℝ) (w : ℂ) : (center s w).im = w.im := by
  simp [center]

lemma displaced_disk_inside
    {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im) :
    closedBall (center s w) (s / 20) ⊆ ball w (w.im / 2) := by
  intro z hz
  have hd := (dist_triangle z (center s w) w).trans
    (add_le_add hz (le_of_eq (center_dist hs.le w)))
  change dist z w < w.im / 2
  linarith

lemma displaced_disk_separated
    {s : ℝ} (hs : 0 < s) (w z : ℂ) (hz : z ∈ closedBall (center s w) (s / 20)) :
    s / 5 ≤ dist z w := by
  have hh := dist_triangle (center s w) z w
  rw [center_dist hs.le w, dist_comm (center s w) z] at hh
  change dist z (center s w) ≤ s / 20 at hz
  linarith

lemma spacing_pos {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m) : 0 < spacing h m := by
  exact div_pos hh (by exact_mod_cast hm)

lemma turnRadius_pos {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m) : 0 < turnRadius h m := by
  unfold turnRadius
  positivity

lemma ribbonWidth_pos {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m) : 0 < ribbonWidth h m := by
  unfold ribbonWidth
  positivity

lemma spacing_eq_width (h : ℝ) (m : ℕ) : spacing h m = 100 * ribbonWidth h m := by
  unfold spacing ribbonWidth
  by_cases hm : m = 0
  · simp [hm]
  · have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp

lemma turnRadius_eq_width (h : ℝ) (m : ℕ) : turnRadius h m = 50 * ribbonWidth h m := by
  unfold turnRadius ribbonWidth
  by_cases hm : m = 0
  · simp [hm]
  · have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp
    ring

lemma columnOffset_bounds {h : ℝ} (hh : 0 < h) {m j : ℕ} (hm : 0 < m)
    (hj : j ≤ 2 * m) : |columnOffset h m j| ≤ h := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hjr : (j : ℝ) ≤ 2 * m := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hq := spacing_pos hh hm
  have hmul : (j : ℝ) * spacing h m ≤ 2 * h := by
    unfold spacing
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hmr).mpr (by nlinarith)
  rw [columnOffset]
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg hj0 hq.le], by linarith⟩

lemma width_le_halfHeight {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m) :
    ribbonWidth h m ≤ h / 100 := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold ribbonWidth
  apply div_le_div_of_nonneg_left hh.le (by norm_num)
  nlinarith

lemma radius_le_halfHeight {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m) :
    turnRadius h m ≤ h / 2 := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold turnRadius
  apply div_le_div_of_nonneg_left hh.le (by norm_num)
  nlinarith

lemma columnPoint_bound {h : ℝ} (hh : 0 < h) {m j : ℕ} (hm : 0 < m)
    (hj : j ≤ 2 * m) (c : ℂ) {y a : ℝ} (hy : |y| ≤ h) (ha : |a| ≤ 1) :
    dist (columnPoint c h m j y a) c ≤ 3 * h := by
  have ho := columnOffset_bounds hh hm hj
  have he := width_le_halfHeight hh hm
  have hwp := (ribbonWidth_pos hh hm).le
  have hprod : |side j * ribbonWidth h m * a| ≤ ribbonWidth h m := by
    rw [abs_mul, abs_mul, side_abs, one_mul, abs_of_nonneg hwp]
    exact mul_le_of_le_one_right hwp ha
  have hx : |columnOffset h m j - side j * ribbonWidth h m * a| ≤
      |columnOffset h m j| + |side j * ribbonWidth h m * a| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (columnOffset h m j) (-(side j * ribbonWidth h m * a))
  have hn := Complex.norm_le_abs_re_add_abs_im
    (((columnOffset h m j - side j * ribbonWidth h m * a : ℝ) : ℂ) +
      (y : ℂ) * Complex.I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, mul_one, zero_add] at hn
  rw [columnPoint, add_assoc, dist_self_add_left]
  linarith

lemma turnPoint_zero (c : ℂ) (h : ℝ) (m j : ℕ) (a : ℝ) :
    turnPoint c h m j 0 a = columnPoint c h m j (side j * h) a := by
  apply Complex.ext
  · simp [turnPoint, columnPoint]
    ring
  · simp [turnPoint, columnPoint]

lemma side_succ (j : ℕ) : side (j + 1) = -side j := by
  by_cases h : Even j <;> simp [side, Nat.even_add_one, h]

lemma turnPoint_pi (c : ℂ) (h : ℝ) (m j : ℕ) (a : ℝ) :
    turnPoint c h m j Real.pi a = columnPoint c h m (j + 1) (side j * h) a := by
  have he : spacing h m = 2 * turnRadius h m := by
    rw [spacing_eq_width, turnRadius_eq_width]
    ring
  apply Complex.ext
  · simp [turnPoint, columnPoint, columnOffset, side_succ, Nat.cast_add, Nat.cast_one]
    nlinarith
  · simp [turnPoint, columnPoint, columnOffset, side_succ, Nat.cast_add, Nat.cast_one]

lemma turn_direction_norm (j : ℕ) (t : ℝ) :
    ‖((-Real.cos t : ℝ) : ℂ) + (side j * Real.sin t : ℂ) * Complex.I‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, mul_one, zero_add]
  calc
    _ = Real.cos t ^ 2 + side j ^ 2 * Real.sin t ^ 2 := by ring
    _ = 1 ^ 2 := by rw [side_sq, one_mul]; nlinarith [Real.sin_sq_add_cos_sq t]

lemma turnPoint_bound {h : ℝ} (hh : 0 < h) {m j : ℕ} (hm : 0 < m)
    (hj : j + 1 ≤ 2 * m) (c : ℂ) (t : ℝ) {a : ℝ} (ha : |a| ≤ 1) :
    dist (turnPoint c h m j t a) c ≤ 4 * h := by
  have ho := columnOffset_bounds hh hm (show j ≤ 2 * m by omega)
  have hr := radius_le_halfHeight hh hm
  have hw := width_le_halfHeight hh hm
  have hrp := (turnRadius_pos hh hm).le
  have hwp := (ribbonWidth_pos hh hm).le
  have hprod : |side j * ribbonWidth h m * a| ≤ ribbonWidth h m := by
    rw [abs_mul, abs_mul, side_abs, one_mul, abs_of_nonneg hwp]
    exact mul_le_of_le_one_right hwp ha
  have hadd := abs_add_le (turnRadius h m) (side j * ribbonWidth h m * a)
  rw [abs_of_nonneg hrp] at hadd
  have hcen := abs_add_le (columnOffset h m j) (turnRadius h m)
  rw [abs_of_nonneg hrp] at hcen
  have hn : ‖((columnOffset h m j + turnRadius h m : ℝ) : ℂ) +
      (side j * h : ℂ) * Complex.I +
      ((turnRadius h m + side j * ribbonWidth h m * a : ℝ) : ℂ) *
        ((-Real.cos t : ℝ) + (side j * Real.sin t : ℂ) * Complex.I)‖ ≤
      |columnOffset h m j + turnRadius h m| + h +
        |turnRadius h m + side j * ribbonWidth h m * a| := by
    calc
      _ ≤ (‖((columnOffset h m j + turnRadius h m : ℝ) : ℂ)‖ +
        ‖(side j * h : ℂ) * Complex.I‖) +
        ‖((turnRadius h m + side j * ribbonWidth h m * a : ℝ) : ℂ) *
          ((-Real.cos t : ℝ) + (side j * Real.sin t : ℂ) * Complex.I)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
          mul_one, side_abs, one_mul, abs_of_pos hh, turn_direction_norm]
  have he : turnPoint c h m j t a - c =
      ((columnOffset h m j + turnRadius h m : ℝ) : ℂ) +
      (side j * h : ℂ) * Complex.I +
      ((turnRadius h m + side j * ribbonWidth h m * a : ℝ) : ℂ) *
        ((-Real.cos t : ℝ) + (side j * Real.sin t : ℂ) * Complex.I) := by
    unfold turnPoint
    ring
  rw [dist_eq_norm, he]
  linarith

lemma column_inside_displaced_disk {s : ℝ} (hs : 0 < s) (w : ℂ)
    {m j : ℕ} (hm : 0 < m) (hj : j ≤ 2 * m) {y a : ℝ}
    (hy : |y| ≤ halfHeight s) (ha : |a| ≤ 1) :
    columnPoint (center s w) (halfHeight s) m j y a ∈ closedBall (center s w) (s / 20) := by
  have hh : 0 < halfHeight s := by unfold halfHeight; positivity
  have hb := columnPoint_bound hh hm hj (center s w) hy ha
  change dist _ _ ≤ s / 20
  dsimp only [halfHeight] at hb ⊢
  linarith


@[simp] lemma columnPoint_re (c : ℂ) (h : ℝ) (m j : ℕ) (y a : ℝ) :
    (columnPoint c h m j y a).re = c.re + columnOffset h m j - side j * ribbonWidth h m * a := by
  simp [columnPoint]
  ring

@[simp] lemma columnPoint_im (c : ℂ) (h : ℝ) (m j : ℕ) (y a : ℝ) :
    (columnPoint c h m j y a).im = c.im + y := by simp [columnPoint]

lemma column_separation {h : ℝ} (hh : 0 < h) {m i j : ℕ} (hm : 0 < m)
    (hij : i < j) (c : ℂ) (y y' : ℝ) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    98 * ribbonWidth h m ≤
      dist (columnPoint c h m i y a) (columnPoint c h m j y' b) := by
  have hepos := (ribbonWidth_pos hh hm).le
  have hnoise (n : ℕ) (u : ℝ) (hu : |u| ≤ 1) :
      |side n * ribbonWidth h m * u| ≤ ribbonWidth h m := by
    rw [abs_mul, abs_mul, side_abs, one_mul, abs_of_nonneg hepos]
    exact mul_le_of_le_one_right hepos hu
  have hai := abs_le.mp (hnoise i a ha)
  have hbj := abs_le.mp (hnoise j b hb)
  have hijr : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hij
  have hmul := mul_le_mul_of_nonneg_right hijr (spacing_pos hh hm).le
  have hre : 98 * ribbonWidth h m ≤
      (columnPoint c h m j y' b).re - (columnPoint c h m i y a).re := by
    simp only [columnPoint_re, columnOffset] at *
    rw [spacing_eq_width] at hmul ⊢
    nlinarith
  calc
    _ ≤ (columnPoint c h m j y' b).re - (columnPoint c h m i y a).re := hre
    _ ≤ |(columnPoint c h m j y' b).re - (columnPoint c h m i y a).re| := le_abs_self _
    _ ≤ dist (columnPoint c h m i y a) (columnPoint c h m j y' b) := by
      simpa only [dist_eq_norm, Complex.sub_re, abs_sub_comm] using
        Complex.abs_re_le_norm (columnPoint c h m i y a - columnPoint c h m j y' b)

lemma columnPoint_ne {h : ℝ} (hh : 0 < h) {m i j : ℕ} (hm : 0 < m)
    (hij : i < j) (c : ℂ) (y y' : ℝ) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    columnPoint c h m i y a ≠ columnPoint c h m j y' b := by
  intro he
  have hd := column_separation hh hm hij c y y' ha hb
  rw [he, dist_self] at hd
  have hp := ribbonWidth_pos hh hm
  linarith


lemma turn_radial_coefficient_pos {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m)
    (j : ℕ) {a : ℝ} (ha : |a| ≤ 1) :
    0 < turnRadius h m + side j * ribbonWidth h m * a := by
  have he := ribbonWidth_pos hh hm
  have hb : |side j * ribbonWidth h m * a| ≤ ribbonWidth h m := by
    rw [abs_mul, abs_mul, side_abs, one_mul, abs_of_pos he]
    exact mul_le_of_le_one_right he.le ha
  rw [turnRadius_eq_width]
  linarith [(abs_le.mp hb).1]

/-- Each circular turn, with its full normal band, is embedded. -/
theorem turnPoint_injective {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m)
    (c : ℂ) (j : ℕ) {t u a b : ℝ} (ht : t ∈ Icc 0 Real.pi)
    (hu : u ∈ Icc 0 Real.pi) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (he : turnPoint c h m j t a = turnPoint c h m j u b) : t = u ∧ a = b := by
  let z := c + ((columnOffset h m j + turnRadius h m : ℝ) : ℂ) +
    (side j * h : ℂ) * Complex.I
  have hn (v q : ℝ) (hq : |q| ≤ 1) : dist (turnPoint c h m j v q) z =
      turnRadius h m + side j * ribbonWidth h m * q := by
    change dist (z + _) z = _
    rw [dist_self_add_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      turn_direction_norm, mul_one, abs_of_pos (turn_radial_coefficient_pos hh hm j hq)]
  have hcoef := congrArg (fun w => dist w z) he
  rw [hn t a ha, hn u b hb] at hcoef
  have hs : side j ≠ 0 := by
    intro hz
    have hn := side_abs j
    rw [hz, abs_zero] at hn
    norm_num at hn
  have hab : a = b := by
    apply mul_left_cancel₀ (ribbonWidth_pos hh hm).ne'
    apply mul_left_cancel₀ hs
    nlinarith [hcoef]
  subst b
  have hre := congrArg Complex.re he
  simp only [turnPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    zero_sub, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] at hre
  have hcos : Real.cos t = Real.cos u := by
    nlinarith [turn_radial_coefficient_pos hh hm j ha]
  exact ⟨Real.injOn_cos ht hu hcos, rfl⟩


end SLEExactGauge.Serpentine

end

end OAI
