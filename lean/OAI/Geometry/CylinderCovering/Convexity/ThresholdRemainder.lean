import Mathlib

namespace OAI

namespace CylinderCovering.ThresholdRemainder

theorem inverse_threshold_remainder
    {e x y Y T α a b c Py PY L : ℝ}
    (he : 0 ≤ e) (hL : 1 ≤ L) (hsmall : 4 * e * L ≤ 1)
    (hx : |x| ≤ 1) (hα : |α| ≤ 1)
    (ha : |a| ≤ L) (hP : |Py| ≤ L)
    (haLip : |a + c| ≤ L * (|Y - y| + |T|))
    (hbLip : |b - α * Y| ≤ L * |T|)
    (hPLip : |PY - Py| ≤ L * |Y - y|)
    (hY : y = Y + e * x * a)
    (hT : T + e * x * b = e * α * x * y +
      e ^ 2 * (α * x ^ 2 * c - Py)) :
    |T| ≤ 3 * L * e ^ 2 ∧ |T + e ^ 2 * PY| ≤ 8 * L ^ 2 * e ^ 3 := by
  have hL0 : 0 ≤ L := by linarith
  have he1 : e ≤ 1 := by nlinarith
  have heL : e * L ≤ 1 / 4 := by linarith
  have hdis : |Y - y| ≤ e * L := by
    rw [hY]
    have hid : Y - (Y + e * x * a) = -(e * x * a) := by ring
    rw [hid, abs_neg, abs_mul, abs_mul, abs_of_nonneg he]
    calc
      e * |x| * |a| ≤ e * 1 * L := by gcongr
      _ = e * L := by ring
  have hax : |α * x ^ 2| ≤ 1 := by
    rw [abs_mul, abs_pow]
    have hx2 : |x| ^ 2 ≤ 1 := by nlinarith only [hx, abs_nonneg x]
    exact (mul_le_mul hα hx2 (by positivity) (by norm_num)).trans_eq (by norm_num)
  have hid : T + e ^ 2 * Py =
      e ^ 2 * (α * x ^ 2) * (a + c) - e * x * (b - α * Y) := by
    rw [hY] at hT
    nlinarith only [hT]
  have herror : |T + e ^ 2 * Py| ≤
      e ^ 2 * L * (e * L + |T|) + e * L * |T| := by
    rw [hid]
    calc
      _ ≤ |e ^ 2 * (α * x ^ 2) * (a + c)| + |e * x * (b - α * Y)| :=
        abs_sub _ _
      _ = e ^ 2 * |α * x ^ 2| * |a + c| + e * |x| * |b - α * Y| := by
        simp only [abs_mul, abs_of_nonneg he, abs_of_nonneg (sq_nonneg e)]
      _ ≤ e ^ 2 * 1 * (L * (e * L + |T|)) + e * 1 * (L * |T|) := by
        gcongr
        exact haLip.trans (mul_le_mul_of_nonneg_left (add_le_add hdis le_rfl) hL0)
      _ = e ^ 2 * L * (e * L + |T|) + e * L * |T| := by ring
  have hcoef : e ^ 2 * L + e * L ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right he1 (mul_nonneg he hL0)
    nlinarith only [h, heL]
  have hsmallterm : e ^ 3 * L ^ 2 ≤ e ^ 2 * L / 4 := by
    have h := mul_le_mul_of_nonneg_right heL (mul_nonneg (sq_nonneg e) hL0)
    nlinarith only [h]
  have hTtri : |T| ≤ |T + e ^ 2 * Py| + e ^ 2 * L := by
    have h := abs_sub (T + e ^ 2 * Py) (e ^ 2 * Py)
    have hPl : |e ^ 2 * Py| ≤ e ^ 2 * L := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg e)]
      exact mul_le_mul_of_nonneg_left hP (sq_nonneg e)
    have hid' : T + e ^ 2 * Py - e ^ 2 * Py = T := by ring
    rw [hid'] at h
    linarith
  have hheight : |T| ≤ 3 * L * e ^ 2 := by
    have hc := mul_le_mul_of_nonneg_right hcoef (abs_nonneg T)
    nlinarith only [hTtri, herror, hc, hsmallterm,
      mul_nonneg (sq_nonneg e) hL0]
  have herror7 : |T + e ^ 2 * Py| ≤ 7 * L ^ 2 * e ^ 3 := by
    have h1 : e ^ 2 * L * |T| ≤ e * L * |T| := by
      have h := mul_le_mul_of_nonneg_right he1
        (mul_nonneg (mul_nonneg he hL0) (abs_nonneg T))
      nlinarith only [h]
    have h2 := mul_le_mul_of_nonneg_left hheight (mul_nonneg he hL0)
    nlinarith only [herror, h1, h2]
  refine ⟨hheight, ?_⟩
  have hPd : |e ^ 2 * (PY - Py)| ≤ L ^ 2 * e ^ 3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg e)]
    calc
      e ^ 2 * |PY - Py| ≤ e ^ 2 * (L * (e * L)) := by gcongr; exact hPLip.trans (mul_le_mul_of_nonneg_left hdis hL0)
      _ = L ^ 2 * e ^ 3 := by ring
  have hh := abs_add_le (T + e ^ 2 * Py) (e ^ 2 * (PY - Py))
  have hsame : T + e ^ 2 * Py + e ^ 2 * (PY - Py) = T + e ^ 2 * PY := by ring
  rw [hsame] at hh
  linarith only [hh, herror7, hPd]

theorem padding_absorbs_at_threshold
    {e L η T P : ℝ} (_he : 0 ≤ e)
    (hheight : |T| ≤ 3 * L * e ^ 2)
    (herror : |T + e ^ 2 * P| ≤ 8 * L ^ 2 * e ^ 3)
    (hmargin : 8 * L ^ 2 * e ≤ η)
    (hcut : 12 * L * e ^ 2 ≤ 1) :
    -(1 / 4 : ℝ) ≤ T ∧ -e ^ 2 * P - η * e ^ 2 ≤ T := by
  have hm := mul_le_mul_of_nonneg_right hmargin (sq_nonneg e)
  constructor
  · linarith only [(abs_le.mp hheight).1, hcut]
  · nlinarith only [(abs_le.mp herror).1, hm]

theorem padding_absorbs_above_threshold
    {e L η T₀ T P₀ P : ℝ} (_he : 0 ≤ e)
    (hheight : |T₀| ≤ 3 * L * e ^ 2)
    (herror : |T₀ + e ^ 2 * P₀| ≤ 8 * L ^ 2 * e ^ 3)
    (hmon : T₀ ≤ T) (hP : |P - P₀| ≤ 2 * L ^ 2 * e)
    (hmargin : 10 * L ^ 2 * e ≤ η)
    (hcut : 12 * L * e ^ 2 ≤ 1) :
    -(1 / 4 : ℝ) ≤ T ∧ -e ^ 2 * P - η * e ^ 2 ≤ T := by
  have hm := mul_le_mul_of_nonneg_right hmargin (sq_nonneg e)
  have hp := mul_le_mul_of_nonneg_left (abs_le.mp hP).1 (sq_nonneg e)
  constructor
  · linarith only [(abs_le.mp hheight).1, hcut, hmon]
  · nlinarith only [(abs_le.mp herror).1, hm, hp, hmon]

theorem padding_absorbs_above_threshold_general
    {e L q T₀ T P₀ P : ℝ}
    (hheight : |T₀| ≤ 3 * L * e ^ 2)
    (herror : |T₀ + e ^ 2 * P₀| ≤ 8 * L ^ 2 * e ^ 3)
    (hmon : T₀ ≤ T) (hP : |P - P₀| ≤ 2 * L ^ 2 * e)
    (hmargin : 10 * L ^ 2 * e ^ 3 ≤ q)
    (hcut : 12 * L * e ^ 2 ≤ 1) :
    -(1 / 4 : ℝ) ≤ T ∧ -e ^ 2 * P - q ≤ T := by
  have hp := mul_le_mul_of_nonneg_left (abs_le.mp hP).1 (sq_nonneg e)
  constructor
  · linarith only [(abs_le.mp hheight).1, hcut, hmon]
  · nlinarith only [(abs_le.mp herror).1, hmargin, hp, hmon]

end CylinderCovering.ThresholdRemainder

end OAI
