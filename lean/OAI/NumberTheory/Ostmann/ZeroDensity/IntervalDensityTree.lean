import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityIncrementTree

namespace OAI

/-! # Equal subdivisions of actual intervals

Cumulative mass functions give exact averaging identities on the interval
partition, so the density-increment tree applies to concrete interval masses.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def intervalNode {M : ℕ} (a L : ℝ) (w : List (Fin M)) : ℝ × ℝ :=
  w.foldl (fun (s : ℝ × ℝ) (i : Fin M) => (s.1 + (i : ℝ) * (s.2 / M), s.2 / M)) (a, L)

noncomputable def intervalNodeDensity {M : ℕ} (φ : ℝ → ℝ) (a L : ℝ)
    (w : List (Fin M)) : ℝ :=
  let s := intervalNode a L w
  (φ (s.1 + s.2) - φ s.1) / s.2

theorem intervalNode_nil {M : ℕ} (a L : ℝ) :
    intervalNode (M := M) a L [] = (a, L) := rfl

theorem intervalNode_child {M : ℕ} (a L : ℝ) (w : List (Fin M)) (i : Fin M) :
    intervalNode a L (w ++ [i]) =
      ((intervalNode a L w).1 + (i : ℝ) * ((intervalNode a L w).2 / M),
        (intervalNode a L w).2 / M) := by
  simp only [intervalNode, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem intervalNode_width_pos {M : ℕ} (hM : 0 < M) (a L : ℝ) (hL : 0 < L)
    (w : List (Fin M)) : 0 < (intervalNode a L w).2 := by
  induction w generalizing a L with
  | nil => exact hL
  | cons i w ih =>
    change 0 < (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).2
    exact ih _ _ (div_pos hL (by exact_mod_cast hM))

private theorem equal_interval_mass_sum {M : ℕ} (hM : 0 < M)
    (φ : ℝ → ℝ) (a L : ℝ) :
    (∑ i : Fin M,
      (φ (a + ((i : ℝ) + 1) * (L / M)) - φ (a + (i : ℝ) * (L / M)))) =
      φ (a + L) - φ a := by
  have hh := Finset.sum_range_sub (fun j : ℕ => φ (a + (j : ℝ) * (L / M))) M
  rw [Finset.sum_range] at hh
  have he : (M : ℝ) * (L / M) = L := by
    have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, he] using hh

theorem intervalNodeDensity_average {M : ℕ} (hM : 0 < M) (φ : ℝ → ℝ)
    (a L : ℝ) (hL : 0 < L) (w : List (Fin M)) :
    (∑ i, intervalNodeDensity φ a L (w ++ [i])) = M * intervalNodeDensity φ a L w := by
  have hW := intervalNode_width_pos hM a L hL w
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [intervalNodeDensity, intervalNode_child]
  have he (i : Fin M) :
      (intervalNode a L w).1 + (i : ℝ) * ((intervalNode a L w).2 / M) +
        (intervalNode a L w).2 / M =
      (intervalNode a L w).1 + ((i : ℝ) + 1) * ((intervalNode a L w).2 / M) := by ring
  simp_rw [he]
  rw [← Finset.sum_div, equal_interval_mass_sum hM]
  field_simp

theorem intervalNode_width {M : ℕ} (_hM : 0 < M) (a L : ℝ) (w : List (Fin M)) :
    (intervalNode a L w).2 = L / (M : ℝ) ^ w.length := by
  induction w generalizing a L with
  | nil => simp [intervalNode]
  | cons i w ih =>
    change (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).2 = _
    rw [ih, List.length_cons, pow_succ]
    ring

theorem intervalNode_bounds {M : ℕ} (hM : 0 < M) (a L : ℝ) (hL : 0 ≤ L)
    (w : List (Fin M)) :
    a ≤ (intervalNode a L w).1 ∧
      (intervalNode a L w).1 + (intervalNode a L w).2 ≤ a + L := by
  induction w generalizing a L with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons i w ih =>
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hiM : (i : ℝ) + 1 ≤ M := by exact_mod_cast i.isLt
    have hq : 0 ≤ L / M := div_nonneg hL hMr.le
    have hbound := mul_le_mul_of_nonneg_right hiM hq
    have he : (M : ℝ) * (L / M) = L := by field_simp
    rw [he] at hbound
    change a ≤ (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).1 ∧ _
    have h := ih (a + (i : ℝ) * (L / M)) (L / M) hq
    constructor
    · exact (le_add_of_nonneg_right (mul_nonneg hi0 hq)).trans h.1
    · change (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).1 +
        (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).2 ≤ a + L
      linarith [h.2]

theorem intervalNode_width_lower {M : ℕ} (hM : 0 < M) (a L : ℝ) (hL : 0 ≤ L)
    (H : ℕ) (w : List (Fin M)) (hw : w.length ≤ H) :
    L / (M : ℝ) ^ H ≤ (intervalNode a L w).2 := by
  rw [intervalNode_width hM]
  apply div_le_div_of_nonneg_left hL (by positivity)
  exact pow_le_pow_right₀ (by exact_mod_cast hM : (1 : ℝ) ≤ M) hw

/-- A concrete cumulative mass function has a rich interval node once its
root density is positive and all relevant interval densities are bounded. -/
theorem exists_rich_interval_node {M : ℕ} (hM : 0 < M) (H : ℕ)
    (φ : ℝ → ℝ) (a L d U : ℝ) (hL : 0 < L) (hd : 0 < d)
    (hroot : d ≤ (φ (a + L) - φ a) / L)
    (hupper : ∀ w : List (Fin M), w.length ≤ H → intervalNodeDensity φ a L w ≤ U)
    (hdepth : U < d + H * (d / (4 * M))) :
    ∃ w : List (Fin M), w.length < H ∧
      ∀ i, d / 2 ≤ intervalNodeDensity φ a L (w ++ [i]) := by
  apply exists_rich_density_node hM H (intervalNodeDensity φ a L) d U hd
  · exact hroot
  · intro w _
    exact intervalNodeDensity_average hM φ a L hL w
  · exact hupper
  · exact hdepth

end Ostmann

end OAI
