import OAI.Analysis.LipschitzHilbert.Trees.DyadicLineGrid

namespace OAI

/-! A uniform interval cover by the nested one-third dyadic grids. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

/-- The elementary one-third covering step at a fixed scale. -/
theorem unit_interval_cover {a b δ : ℝ} (hδ0 : 1 / 3 ≤ δ) (hδ1 : δ ≤ 2 / 3)
    (hlen : b - a < 1 / 3) :
    (∃ j : ℤ, Icc a b ⊆ Ico (j : ℝ) (j + 1)) ∨
      ∃ j : ℤ, Icc a b ⊆ Ico ((j : ℝ) + δ) (j + 1 + δ) := by
  let n : ℤ := ⌊a⌋
  have hn0 : (n : ℝ) ≤ a := Int.floor_le a
  have hn1 : a < (n : ℝ) + 1 := Int.lt_floor_add_one a
  by_cases hb : b < (n : ℝ) + 1
  · left
    refine ⟨n, ?_⟩
    intro x hx
    exact ⟨hn0.trans hx.1, hx.2.trans_lt hb⟩
  · right
    refine ⟨n, ?_⟩
    intro x ⟨hxa, hxb⟩
    constructor <;> linarith [le_of_not_gt hb]

/-- Each interval shorter than one third of a grid cell fits in one cell of
the ordinary or alternating one-third grid. -/
theorem fixed_scale_interval_cover (k : ℤ) {a b : ℝ} (hlen : b - a < scale k / 3) :
    ∃ q ∈ ({0, 1} : Finset ℤ), ∃ j : ℤ, Icc a b ⊆ cell q k j := by
  have hs := scale_pos k
  have hnorm : b / scale k - a / scale k < 1 / 3 := by
    have hh : (b - a) / scale k < 1 / 3 := (div_lt_iff₀ hs).2 (by nlinarith)
    simpa only [sub_div] using hh
  have hsign : (k.negOnePow : ℤ) = 1 ∨ (k.negOnePow : ℤ) = -1 :=
    (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp (Int.abs_negOnePow k)
  rcases hsign with hsign | hsign
  · obtain h | h := unit_interval_cover (δ := 1 / 3) (by norm_num) (by norm_num) hnorm
    · obtain ⟨j, hj⟩ := h
      refine ⟨0, by simp, j, ?_⟩
      intro x hx
      have hn := hj (show x / scale k ∈ Icc (a / scale k) (b / scale k) from
        ⟨(div_le_div_of_nonneg_right hx.1 hs.le), (div_le_div_of_nonneg_right hx.2 hs.le)⟩)
      have h0 := (le_div_iff₀ hs).mp hn.1
      have h1 := (div_lt_iff₀ hs).mp hn.2
      simp only [cell, left, shift, mul_zero, Int.cast_zero, zero_div, add_zero]
      push_cast
      constructor <;> nlinarith
    · obtain ⟨j, hj⟩ := h
      refine ⟨1, by simp, j, ?_⟩
      intro x hx
      have hn := hj (show x / scale k ∈ Icc (a / scale k) (b / scale k) from
        ⟨(div_le_div_of_nonneg_right hx.1 hs.le), (div_le_div_of_nonneg_right hx.2 hs.le)⟩)
      have h0 := (le_div_iff₀ hs).mp hn.1
      have h1 := (div_lt_iff₀ hs).mp hn.2
      simp only [cell, left, shift, hsign, mul_one, Int.cast_one]
      push_cast
      constructor <;> nlinarith
  · obtain h | h := unit_interval_cover (δ := 2 / 3) (by norm_num) (by norm_num) hnorm
    · obtain ⟨j, hj⟩ := h
      refine ⟨0, by simp, j, ?_⟩
      intro x hx
      have hn := hj (show x / scale k ∈ Icc (a / scale k) (b / scale k) from
        ⟨(div_le_div_of_nonneg_right hx.1 hs.le), (div_le_div_of_nonneg_right hx.2 hs.le)⟩)
      have h0 := (le_div_iff₀ hs).mp hn.1
      have h1 := (div_lt_iff₀ hs).mp hn.2
      simp only [cell, left, shift, mul_zero, Int.cast_zero, zero_div, add_zero]
      push_cast
      constructor <;> nlinarith
    · obtain ⟨j, hj⟩ := h
      refine ⟨1, by simp, j + 1, ?_⟩
      intro x hx
      have hn := hj (show x / scale k ∈ Icc (a / scale k) (b / scale k) from
        ⟨(div_le_div_of_nonneg_right hx.1 hs.le), (div_le_div_of_nonneg_right hx.2 hs.le)⟩)
      have h0 := (le_div_iff₀ hs).mp hn.1
      have h1 := (div_lt_iff₀ hs).mp hn.2
      simp only [cell, left, shift, hsign, mul_one, Int.cast_neg, Int.cast_one]
      push_cast
      constructor <;> nlinarith

/-- A positive-length interval is contained in a dyadic interval of length
at most six times its own, with one of two fixed nested grids. -/
theorem interval_cover {a b : ℝ} (hab : a < b) :
    ∃ q ∈ ({0, 1} : Finset ℤ), ∃ k j : ℤ,
      Icc a b ⊆ cell q k j ∧ scale k ≤ 6 * (b - a) := by
  obtain ⟨n, hn0, hn1⟩ := exists_mem_Ico_zpow
    (show (0 : ℝ) < 3 * (b - a) by linarith) (by norm_num : (1 : ℝ) < 2)
  have hlarge : b - a < scale (n + 1) / 3 := by
    change 3 * (b - a) < scale (n + 1) at hn1
    linarith
  obtain ⟨q, hq, j, hj⟩ := fixed_scale_interval_cover (n + 1) hlarge
  refine ⟨q, hq, n + 1, j, hj, ?_⟩
  change scale n ≤ 3 * (b - a) at hn0
  rw [scale_succ]
  linarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI
