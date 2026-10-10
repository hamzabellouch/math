import OAI.Analysis.LipschitzHilbert.Trees.LineGridMartingale
import OAI.Analysis.LipschitzHilbert.Estimates.IntervalPoincare

namespace OAI

/-! Low-frequency averaging errors on the actual nested line grid. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem index_lt_level (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) (x : ℝ) :
    (g.index level x).val < g.branching ^ level := by
  let h : FiniteLineGrid := { g with depth := level }
  have ht := h.rawIndex_lt (le_refl level) x
  change g.rawIndex level x < g.branching ^ level at ht
  simpa only [index, Nat.min_eq_left hl] using ht

theorem cells_cover_root (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) :
    (⋃ i : Fin (g.branching ^ level), g.cell level i.val) = g.root := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact g.cell_subset_root level i.isLt hi
  · intro hx
    let i : Fin (g.branching ^ level) := ⟨(g.index level x).val, g.index_lt_level hl x⟩
    exact mem_iUnion.mpr ⟨i, (g.index_eq_iff_mem_cell hl hx i.val).mp rfl⟩

theorem cells_disjoint (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) :
    Pairwise (fun i j : Fin (g.branching ^ level) => Disjoint (g.cell level i.val) (g.cell level j.val)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hri := g.cell_subset_root level i.isLt hxi
  have hix := (g.index_eq_iff_mem_cell hl hri i.val).mpr hxi
  have hjx := (g.index_eq_iff_mem_cell hl hri j.val).mpr hxj
  exact hij (Fin.ext (hix.symm.trans hjx))

theorem cell_poincare (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) (hdf : Differentiable ℝ f)
    (hd : MemLp (deriv f) 2 volume) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    (∫ x in g.cell level i, |f x - g.average g.lineMeasure f level x| ^ 2) ≤
      g.meshWidth level ^ 2 * ∫ x in g.cell level i, |deriv f x| ^ 2 := by
  let a := g.origin + g.meshWidth level * i
  let b := g.origin + g.meshWidth level * (i + 1)
  have hlength : b - a = g.meshWidth level := by dsimp [a,b]; ring
  have hab : a < b := sub_pos.mp (hlength ▸ g.meshWidth_pos level)
  have h := interval_poincare_Ico f hab (fun x _ => hdf x) (hd.restrict (Icc a b))
  rw [hlength] at h
  calc
    _ = ∫ x in Ico a b, |f x - (g.meshWidth level)⁻¹ * ∫ y in Ico a b, f y| ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      dsimp only
      rw [g.average_eq_cell_mean f hf hl hi hx, div_eq_mul_inv, mul_comm]
      rfl
    _ ≤ _ := by simpa only [Real.norm_eq_abs, smul_eq_mul, cell, a, b] using h

/-- Summing the actual disjoint cells gives the low-frequency part of
the smooth/dyadic comparison, with no loss from their number. -/
theorem poincare (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : MemLp f 2 g.lineMeasure) (hdf : Differentiable ℝ f)
    (hd : MemLp (deriv f) 2 volume) {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, |f x - g.average g.lineMeasure f level x| ^ 2 ∂g.lineMeasure) ≤
      g.meshWidth level ^ 2 * ∫ x in g.root, |deriv f x| ^ 2 := by
  have herr : Integrable (fun x => |f x - g.average g.lineMeasure f level x| ^ 2)
      g.lineMeasure := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hf.sub (g.average_memLp g.lineMeasure f hf level)).integrable_norm_pow (by decide : 2 ≠ 0)
  have hder : Integrable (fun x => |deriv f x| ^ 2) volume := by
    simpa only [Real.norm_eq_abs] using hd.integrable_norm_pow (by decide : 2 ≠ 0)
  have hc (i : Fin (g.branching ^ level)) :
      IntegrableOn (fun x => |f x - g.average g.lineMeasure f level x| ^ 2)
        (g.cell level i.val) volume :=
    herr.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root level i.isLt))
  change (∫ x in g.root, |f x - g.average g.lineMeasure f level x| ^ 2) ≤ _
  have hpartf := integral_iUnion_fintype
    (s := fun i : Fin (g.branching ^ level) => g.cell level i.val)
    (fun _ => measurableSet_Ico) (g.cells_disjoint hl) hc
  have hpartd := integral_iUnion_fintype
    (s := fun i : Fin (g.branching ^ level) => g.cell level i.val)
    (fun _ => measurableSet_Ico) (g.cells_disjoint hl) (fun _ => hder.integrableOn)
  rw [g.cells_cover_root hl] at hpartf hpartd
  rw [hpartf]
  calc
    _ ≤ ∑ i : Fin (g.branching ^ level), g.meshWidth level ^ 2 *
        ∫ x in g.cell level i.val, |deriv f x| ^ 2 :=
      Finset.sum_le_sum fun i _ => g.cell_poincare f (hf.integrable (by norm_num)) hdf hd hl i.isLt
    _ = _ := by
      rw [← Finset.mul_sum, ← hpartd]

end LipschitzHilbert.FiniteLineGrid

end

end OAI
