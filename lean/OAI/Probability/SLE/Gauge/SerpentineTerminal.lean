import OAI.Probability.SLE.Gauge.SerpentineEmbedding

namespace OAI

noncomputable section
open Set

namespace SLEExactGauge.Serpentine

/-- A turn cannot meet any column except its two attached columns,
regardless of the height on that column. -/
theorem turnPoint_column_ne_nonadjacent {h : ℝ} (hh : 0 < h) {m i k : ℕ} (hm : 0 < m)
    (hk : k < i ∨ i + 2 ≤ k) (c : ℂ) (t y : ℝ) {a b : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    turnPoint c h m i t a ≠ columnPoint c h m k y b := by
  intro he
  have ht := abs_le.mp (turn_horizontal_bound hh hm c i t ha)
  have hc := congrArg Complex.re he
  rw [columnPoint_re] at hc
  have hw := ribbonWidth_pos hh hm
  have hb' : |side k * ribbonWidth h m * b| ≤ ribbonWidth h m := by
    rw [abs_mul, abs_mul, side_abs, one_mul, abs_of_pos hw]
    exact mul_le_of_le_one_right hw.le hb
  have hb'' := abs_le.mp hb'
  simp only [columnOffset] at ht hc
  rw [turnRadius_eq_width, spacing_eq_width] at ht
  rw [spacing_eq_width] at hc
  rcases hk with hk | hk
  · have hki : (k : ℝ) + 1 ≤ i := by exact_mod_cast hk
    nlinarith
  · have hik : (i : ℝ) + 2 ≤ k := by exact_mod_cast hk
    nlinarith

lemma side_even (m : ℕ) : side (2 * m) = 1 := by
  simp only [side, ite_eq_left (even_two_mul m)]

/-- The upward terminal continuation is disjoint from every turn.
The preceding turn bends downwards; earlier turns are horizontally
separated from the terminal column. -/
theorem turnPoint_terminal_column_ne {h : ℝ} (hh : 0 < h) {m i : ℕ} (hm : 0 < m)
    (hi : i < 2 * m) (c : ℂ) {t y a b : ℝ} (ht : t ∈ Icc 0 Real.pi)
    (hy : h < y) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    turnPoint c h m i t a ≠ columnPoint c h m (2 * m) y b := by
  by_cases hil : i + 1 = 2 * m
  · intro he
    have hs : side i = -1 := by
      have hh := side_succ i
      rw [hil, side_even] at hh
      linarith
    have hh := turn_oriented_height hh hm c i ht ha
    rw [hs, he, columnPoint_im] at hh
    linarith
  · exact turnPoint_column_ne_nonadjacent hh hm (Or.inr (by omega)) c t y ha hb

end SLEExactGauge.Serpentine

end

end OAI
