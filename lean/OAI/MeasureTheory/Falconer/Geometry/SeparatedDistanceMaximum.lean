import OAI.MeasureTheory.Falconer.Geometry.ComparableCellCounting
import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceRebinBound

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
theorem filtered_pair_sum_le_degree {α : Type*} [DecidableEq α]
    (C : Finset α) (R : α → α → Prop) [DecidableRel R]
    (W : α → α → ℝ≥0∞) (degree : ℕ)
    (hd : ∀ row ∈ C, (C.filter (R row)).card ≤ degree) :
    (∑ row ∈ C, ∑ col ∈ C, if R row col then W row col else 0) ≤
      (C.card:ℝ≥0∞)*(degree:ℝ≥0∞)*
        ((C ×ˢ C).filter (fun z => R z.1 z.2)).sup (fun z => W z.1 z.2) := by
  let U := ((C ×ˢ C).filter (fun z => R z.1 z.2)).sup (fun z => W z.1 z.2)
  have hrow (row : α) (hr : row ∈ C) :
      (∑ col ∈ C, if R row col then W row col else 0) ≤ (degree:ℝ≥0∞)*U := by
    rw [← Finset.sum_filter]
    have hle (col : α) (hc : col ∈ C.filter (R row)) : W row col ≤ U := by
      exact Finset.le_sup (s := (C ×ˢ C).filter (fun z => R z.1 z.2))
        (b := (row,col)) (f := fun z => W z.1 z.2)
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,(Finset.mem_filter.mp hc).1⟩,
          (Finset.mem_filter.mp hc).2⟩)
    have hh := Finset.sum_le_sum hle
    rw [Finset.sum_const,nsmul_eq_mul] at hh
    have hhdeg : ((C.filter (R row)).card:ℝ≥0∞) ≤ (degree:ℝ≥0∞) := Nat.cast_le.mpr (hd row hr)
    exact hh.trans (mul_le_mul_left hhdeg U)
  have hh := Finset.sum_le_sum hrow
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_assoc,U] using hh

namespace PositiveDistanceData

noncomputable def separatedMaximum (d e : PositiveDistanceData)
    (C : Finset (CellPath × CellPath)) (b : ℕ) : ℝ≥0∞ :=
  ((C ×ˢ C).filter (fun z => angularSeparated d.Q e.Q b z.1 z.2)).sup
    (fun z => max (d.atCells z.1.1 z.2.1).coincidence (e.atCells z.1.2 z.2.2).coincidence)

theorem separatedMaximum_ne_top (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (C : Finset (CellPath × CellPath)) (b : ℕ) : d.separatedMaximum e C b ≠ ⊤ := by
  apply ne_of_lt
  apply Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < ⊤) |>.mpr
  intro z hz
  exact max_lt (lt_top_iff_ne_top.mpr (coincidence_ne_top _))
    (lt_top_iff_ne_top.mpr (coincidence_ne_top _))

theorem separated_sum_le_degree (d e : PositiveDistanceData)
    (b : ℕ) (C : Finset (CellPath × CellPath)) (degree : ℕ)
    (hdegree : ∀ row ∈ C, (C.filter (angularSeparated d.Q e.Q b row)).card ≤ degree) :
    (∑ row ∈ C, ∑ col ∈ C, if angularSeparated d.Q e.Q b row col then
      max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence else 0) ≤
      (C.card : ℝ≥0∞)*(degree:ℝ≥0∞)*d.separatedMaximum e C b := by
  exact filtered_pair_sum_le_degree C (angularSeparated d.Q e.Q b)
    (fun row col => max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence) degree hdegree

theorem separated_sum_le_maximum (d e : PositiveDistanceData)
    (hQ : d.Q.side = 1) (hQ' : e.Q.side = 1) (b : ℕ)
    (C : Finset (CellPath × CellPath)) (hC : C ⊆ (dyadicPaths b) ×ˢ (dyadicPaths b)) :
    (∑ row ∈ C, ∑ col ∈ C, if angularSeparated d.Q e.Q b row col then
      max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence else 0) ≤
      (C.card : ℝ≥0∞)*257025537024256*d.separatedMaximum e C b := by
  simpa only [Nat.cast_ofNat] using separated_sum_le_degree d e b C 257025537024256
    (fun row _ => angularSeparated_degree d.Q e.Q hQ hQ' b C hC row)

end PositiveDistanceData

end PlanarFalconer

end OAI
