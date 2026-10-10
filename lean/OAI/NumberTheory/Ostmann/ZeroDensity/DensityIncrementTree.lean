import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Finite density increment for selecting a rich block

A low-density child of a block forces a definite increase in another child.
Iterating cannot exceed a fixed upper density, so a block with no low child
occurs before a bounded depth.
-/

namespace Ostmann

open scoped BigOperators Classical

private theorem density_child_increment {M : ℕ} (hM : 0 < M)
    (x : Fin M → ℝ) (D d : ℝ) (hd : 0 < d) (hD : d ≤ D)
    (hmean : ∑ i, x i = M * D) (hbad : ∃ i, x i < d / 2) :
    ∃ i, D + d / (4 * M) ≤ x i := by
  obtain ⟨i, hi⟩ := hbad
  by_contra! h
  have hsum : (∑ j ∈ Finset.univ.erase i, x j) ≤
      ((Finset.univ.erase i).card : ℝ) * (D + d / (4 * M)) := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, (D + d / (4 * M)) :=
        Finset.sum_le_sum (fun j _ => (h j).le)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.erase i).card : ℝ) = (M : ℝ) - 1 := by
    have hh := Finset.card_erase_add_one (Finset.mem_univ i)
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    have hh' : ((Finset.univ.erase i).card : ℝ) + 1 = M := by exact_mod_cast hh
    linarith
  have heq := Finset.sum_erase_add (Finset.univ : Finset (Fin M)) x (Finset.mem_univ i)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (M : ℝ) * (d / (4 * M)) = d / 4 := by field_simp
  rw [hcard] at hsum
  nlinarith [div_nonneg hd.le (by positivity : (0 : ℝ) ≤ 4 * M)]

/-- The fixed increment forces a rich node before the density ceiling is
reached. A node is an actual ordered list of child choices. -/
theorem exists_rich_density_node {M : ℕ} (hM : 0 < M) (H : ℕ)
    (D : List (Fin M) → ℝ) (d U : ℝ) (hd : 0 < d)
    (hroot : d ≤ D [])
    (hmean : ∀ w, w.length < H → (∑ i, D (w ++ [i])) = M * D w)
    (hupper : ∀ w, w.length ≤ H → D w ≤ U)
    (hdepth : U < d + H * (d / (4 * M))) :
    ∃ w : List (Fin M), w.length < H ∧ ∀ i, d / 2 ≤ D (w ++ [i]) := by
  let ε := d / (4 * M)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsteps : ∀ j ≤ H,
      (∃ w : List (Fin M), w.length < j ∧ ∀ i, d / 2 ≤ D (w ++ [i])) ∨
      ∃ w : List (Fin M), w.length = j ∧ d + j * ε ≤ D w := by
    intro j
    induction j with
    | zero => intro _; exact Or.inr ⟨[], rfl, by simpa using hroot⟩
    | succ j ih =>
      intro hj
      rcases ih (by omega) with ⟨w, hw, hgood⟩ | ⟨w, hw, hD⟩
      · exact Or.inl ⟨w, by omega, hgood⟩
      · by_cases hgood : ∀ i, d / 2 ≤ D (w ++ [i])
        · exact Or.inl ⟨w, by omega, hgood⟩
        · have hbad : ∃ i, D (w ++ [i]) < d / 2 := by simpa using hgood
          obtain ⟨i, hi⟩ := density_child_increment hM (fun i => D (w ++ [i])) (D w) d hd
            (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hε.le])
            (hmean w (by omega)) hbad
          right
          refine ⟨w ++ [i], by simp [hw], ?_⟩
          change D w + ε ≤ D (w ++ [i]) at hi
          push_cast
          linarith
  rcases hsteps H le_rfl with h | ⟨w, hw, hD⟩
  · exact h
  · have hu := hupper w hw.le
    exact False.elim (by dsimp [ε] at hD; linarith)

end Ostmann

end OAI
