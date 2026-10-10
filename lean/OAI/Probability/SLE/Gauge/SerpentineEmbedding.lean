import OAI.Probability.SLE.Gauge.SerpentineLayout

namespace OAI

/-! The only contacts between the straight and circular normal bands are
their prescribed common end sections. These geometric statements support
the global embedding of the concatenated serpentine. -/

noncomputable section
open Set

namespace SLEExactGauge.Serpentine

@[simp] lemma turnPoint_im (c : ℂ) (h : ℝ) (m j : ℕ) (t a : ℝ) :
    (turnPoint c h m j t a).im = c.im + side j * h +
      (turnRadius h m + side j * ribbonWidth h m * a) * (side j * Real.sin t) := by
  simp only [turnPoint, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_add]

lemma turnPoint_oriented_im (c : ℂ) (h : ℝ) (m j : ℕ) (t a : ℝ) :
    side j * ((turnPoint c h m j t a).im - c.im) =
      h + (turnRadius h m + side j * ribbonWidth h m * a) * Real.sin t := by
  rw [turnPoint_im]
  let R := turnRadius h m + side j * ribbonWidth h m * a
  change side j * (c.im + side j * h + R * (side j * Real.sin t) - c.im) = h + R * Real.sin t
  calc
    _ = side j ^ 2 * (h + R * Real.sin t) := by ring
    _ = _ := by rw [side_sq, one_mul]

lemma columnPoint_equal_forces_index {h : ℝ} (hh : 0 < h) {m i j : ℕ} (hm : 0 < m)
    (c : ℂ) (y y' : ℝ) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (he : columnPoint c h m i y a = columnPoint c h m j y' b) : i = j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · exact columnPoint_ne hh hm hij c y y' ha hb he
  · exact columnPoint_ne hh hm hji c y' y hb ha he.symm

lemma columnPoint_injective {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m)
    (c : ℂ) (j : ℕ) {y y' a b : ℝ}
    (he : columnPoint c h m j y a = columnPoint c h m j y' b) : y = y' ∧ a = b := by
  have hy := congrArg Complex.im he
  simp only [columnPoint_im] at hy
  have ha := congrArg Complex.re he
  simp only [columnPoint_re] at ha
  have hs : side j ≠ 0 := by
    intro hz
    have hh := side_abs j
    rw [hz, abs_zero] at hh
    norm_num at hh
  refine ⟨by linarith, ?_⟩
  apply mul_left_cancel₀ (mul_ne_zero hs (ribbonWidth_pos hh hm).ne')
  nlinarith

/-- A circular normal band can meet a straight band only at angle zero
or pi; its interior lies strictly above or below all straight passes. -/
theorem turnPoint_column_contact {h : ℝ} (hh : 0 < h) {m j k : ℕ} (hm : 0 < m)
    (c : ℂ) {t y a b : ℝ} (ht : t ∈ Icc 0 Real.pi) (hy : |y| ≤ h)
    (ha : |a| ≤ 1) (he : turnPoint c h m j t a = columnPoint c h m k y b) :
    t = 0 ∨ t = Real.pi := by
  by_contra hn
  push Not at hn
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (lt_of_le_of_ne ht.1 (Ne.symm hn.1)) (lt_of_le_of_ne ht.2 hn.2)
  have hor := turnPoint_oriented_im c h m j t a
  have hcoeff := turn_radial_coefficient_pos hh hm j ha
  have hy' : |(turnPoint c h m j t a).im - c.im| ≤ h := by
    rw [he, columnPoint_im, add_sub_cancel_left]
    exact hy
  have hu : side j * ((turnPoint c h m j t a).im - c.im) ≤ h := by
    calc
      _ ≤ |side j * ((turnPoint c h m j t a).im - c.im)| := le_abs_self _
      _ = |(turnPoint c h m j t a).im - c.im| := by rw [abs_mul, side_abs, one_mul]
      _ ≤ h := hy'
  nlinarith [mul_pos hcoeff hsin]

/-- Exact gluing sections, including the matching normal coordinate. -/
theorem turnPoint_column_gluing {h : ℝ} (hh : 0 < h) {m j k : ℕ} (hm : 0 < m)
    (c : ℂ) {t y a b : ℝ} (ht : t ∈ Icc 0 Real.pi) (hy : |y| ≤ h)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (he : turnPoint c h m j t a = columnPoint c h m k y b) :
    (t = 0 ∧ k = j ∧ y = side j * h ∧ a = b) ∨
      (t = Real.pi ∧ k = j + 1 ∧ y = side j * h ∧ a = b) := by
  rcases turnPoint_column_contact hh hm c ht hy ha he with rfl | rfl
  · rw [turnPoint_zero] at he
    have hk := columnPoint_equal_forces_index hh hm c (side j * h) y ha hb he
    subst k
    obtain ⟨hy', ha'⟩ := columnPoint_injective hh hm c j he
    exact Or.inl ⟨rfl, rfl, hy'.symm, ha'⟩
  · rw [turnPoint_pi] at he
    have hk := columnPoint_equal_forces_index hh hm c (side j * h) y ha hb he
    subst k
    obtain ⟨hy', ha'⟩ := columnPoint_injective hh hm c (j + 1) he
    exact Or.inr ⟨rfl, rfl, hy'.symm, ha'⟩

@[simp] lemma turnPoint_re (c : ℂ) (h : ℝ) (m j : ℕ) (t a : ℝ) :
    (turnPoint c h m j t a).re = c.re + columnOffset h m j + turnRadius h m -
      (turnRadius h m + side j * ribbonWidth h m * a) * Real.cos t := by
  simp only [turnPoint, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_add]
  ring

lemma turn_horizontal_bound {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m)
    (c : ℂ) (j : ℕ) (t : ℝ) {a : ℝ} (ha : |a| ≤ 1) :
    |(turnPoint c h m j t a).re - (c.re + columnOffset h m j + turnRadius h m)| ≤
      turnRadius h m + ribbonWidth h m := by
  have hr := (turnRadius_pos hh hm).le
  have hw := (ribbonWidth_pos hh hm).le
  have hb : |side j * ribbonWidth h m * a| ≤ ribbonWidth h m := by
    rw [abs_mul, abs_mul, side_abs, one_mul, abs_of_nonneg hw]
    exact mul_le_of_le_one_right hw ha
  have ha' := abs_add_le (turnRadius h m) (side j * ribbonWidth h m * a)
  rw [abs_of_nonneg hr] at ha'
  rw [turnPoint_re]
  have he : c.re + columnOffset h m j + turnRadius h m -
      (turnRadius h m + side j * ribbonWidth h m * a) * Real.cos t -
      (c.re + columnOffset h m j + turnRadius h m) =
      -((turnRadius h m + side j * ribbonWidth h m * a) * Real.cos t) := by ring
  rw [he, abs_neg, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one t)).trans (ha'.trans (by linarith))

lemma turn_oriented_height {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 0 < m)
    (c : ℂ) (j : ℕ) {t a : ℝ} (ht : t ∈ Icc 0 Real.pi) (ha : |a| ≤ 1) :
    h ≤ side j * ((turnPoint c h m j t a).im - c.im) := by
  rw [turnPoint_oriented_im]
  exact le_add_of_nonneg_right (mul_nonneg (turn_radial_coefficient_pos hh hm j ha).le
    (Real.sin_nonneg_of_mem_Icc ht))

/-- Different circular turns have disjoint full normal bands. Neighboring
turns lie on opposite sides; all other turn pairs have horizontal clearance. -/
theorem turnPoint_ne {h : ℝ} (hh : 0 < h) {m i j : ℕ} (hm : 0 < m)
    (hij : i < j) (c : ℂ) {t u a b : ℝ} (ht : t ∈ Icc 0 Real.pi)
    (hu : u ∈ Icc 0 Real.pi) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    turnPoint c h m i t a ≠ turnPoint c h m j u b := by
  intro he
  by_cases hnext : j = i + 1
  · subst j
    have h₁ := turn_oriented_height hh hm c i ht ha
    have h₂ := turn_oriented_height hh hm c (i + 1) hu hb
    rw [← he, side_succ] at h₂
    nlinarith
  · have hfar : i + 2 ≤ j := by omega
    have hfar' : (i : ℝ) + 2 ≤ j := by exact_mod_cast hfar
    have hstep := mul_le_mul_of_nonneg_right hfar' (spacing_pos hh hm).le
    have h₁ := abs_le.mp (turn_horizontal_bound hh hm c i t ha)
    have h₂ := abs_le.mp (turn_horizontal_bound hh hm c j u hb)
    rw [← he] at h₂
    simp only [columnOffset] at h₁ h₂
    rw [spacing_eq_width] at hstep h₁ h₂
    rw [turnRadius_eq_width] at h₁ h₂
    have hw := ribbonWidth_pos hh hm
    nlinarith


end SLEExactGauge.Serpentine

end

end OAI
