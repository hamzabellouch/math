import OAI.MeasureTheory.Falconer.Recursion.ProfileGridCells

namespace OAI

/-! Preserve the analytic bounds when the chosen profile intervals are
rounded inward to the finite scale grid. -/
namespace Falconer
open Set

private theorem rounded_error_change {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) (hc : 0 < c.2)
    (hd : 0 < (innerProfileCell n c).2) {x : ℝ}
    (hx : x ∈ Icc (innerProfileCell n c).1
      ((innerProfileCell n c).1+(innerProfileCell n c).2)) :
    |intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x-
      intervalSecantError f c.1 c.2 x| ≤ 4/(n : ℝ) := by
  have hb := profileGrid_interval_bounds hn c.1 c.2
  have hend : profileGridLeft n c.1+(innerProfileCell n c).2 =
      profileGridRight n (c.1+c.2) := innerProfileCell_end n c
  have he := intervalSecantError_grid_stability hf c.1 hc hd hb.2.2.1
    (by rw [hend]; exact hb.2.2.2) hx
  exact he.trans_eq (by ring)

private theorem rounded_interval_subset {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) :
    Icc (innerProfileCell n c).1 ((innerProfileCell n c).1+(innerProfileCell n c).2) ⊆
      Icc c.1 (c.1+c.2) := by
  intro x hx
  rw [innerProfileCell_end] at hx
  exact ⟨(profileGridLeft_bounds hn c.1).1.trans hx.1,
    hx.2.trans (profileGridRight_bounds hn (c.1+c.2)).2⟩

theorem rounded_profile_linear_error {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) (hc : 0 < c.2)
    (hd : 0 < (innerProfileCell n c).2) {ε : ℝ}
    (herr : ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ ε*c.2)
    {x : ℝ} (hx : x ∈ Icc (innerProfileCell n c).1
      ((innerProfileCell n c).1+(innerProfileCell n c).2)) :
    |intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x| ≤
      ε*c.2+4/(n : ℝ) := by
  have he := rounded_error_change hf hn c hc hd hx
  have ho := herr x (rounded_interval_subset hn c hx)
  have ht := abs_add_le
    (intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x-
      intervalSecantError f c.1 c.2 x) (intervalSecantError f c.1 c.2 x)
  rw [sub_add_cancel] at ht
  linarith

theorem rounded_profile_superlinear_error {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) (hc : 0 < c.2)
    (hd : 0 < (innerProfileCell n c).2) {ε : ℝ}
    (herr : ∀ x ∈ Icc c.1 (c.1+c.2), -ε*c.2 ≤ intervalSecantError f c.1 c.2 x)
    {x : ℝ} (hx : x ∈ Icc (innerProfileCell n c).1
      ((innerProfileCell n c).1+(innerProfileCell n c).2)) :
    -ε*c.2-4/(n : ℝ) ≤ intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x := by
  have he := (abs_le.mp (rounded_error_change hf hn c hc hd hx)).1
  have ho := herr x (rounded_interval_subset hn c hx)
  linarith

theorem rounded_profile_slope_error {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ) (hc : 0 < c.2)
    (hd : 0 < (innerProfileCell n c).2) :
    |intervalSecantSlope f (innerProfileCell n c).1 (innerProfileCell n c).2-
      intervalSecantSlope f c.1 c.2| ≤ 8/((n : ℝ)*(innerProfileCell n c).2) := by
  have hb := profileGrid_interval_bounds hn c.1 c.2
  have hend : profileGridLeft n c.1+(innerProfileCell n c).2 =
      profileGridRight n (c.1+c.2) := innerProfileCell_end n c
  have he := intervalSecantSlope_grid_stability hf c.1 hc hd hb.2.2.1
    (by rw [hend]; exact hb.2.2.2)
  exact he.trans_eq (by ring)

end Falconer

end OAI
