import OAI.MeasureTheory.Falconer.Estimates.ActualSuccessorUpperBounds
import OAI.MeasureTheory.Falconer.Recursion.ReachedStateRecursion

namespace OAI

namespace PlanarFalconer
open MeasureTheory

namespace PositiveDistanceData

def RecursiveCells (d : PositiveDistanceData) : Prop :=
  d.X.length = d.a ∧ d.Y.length = d.a ∧
  100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ∧
  dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ))

theorem RecursiveCells.stronglySeparated {d : PositiveDistanceData}
    (h : d.RecursiveCells) (hQ : d.Q.side = 1) : d.StronglySeparated :=
  d.stronglySeparated_of_unit hQ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem RecursiveCells.update {d : PositiveDistanceData} (h : d.RecursiveCells) (t i : ℕ) :
    ({d with t := t,i := i} : PositiveDistanceData).RecursiveCells := h

theorem angularSuccessor_lengths (d : PositiveDistanceData) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) (v : ℕ)
    {row : CellPath × CellPath}
    (hr : row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a)) :
    (d.angularSuccessor p v row).X.length = p ∧
      (d.angularSuccessor p v row).Y.length = p := by
  change row.1.length = p ∧ row.2.length = p
  have hm := sourceProductVertices_subset d.Q d.Q d.ρ d.ρ d.X d.Y d.a (p-d.a) hX hY hr
  have hm := Finset.mem_product.mp hm
  exact ⟨by simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hm.1,
    by simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hm.2⟩

theorem angularSuccessor_budget (d : PositiveDistanceData) (p v : ℕ)
    (row : CellPath × CellPath) {Kinv K : ℕ} (hK : Kinv ≤ K)
    (k : Fin 2 → PolicyDescriptor → ℕ)
    (hk : ∀ l, ∑ e ∈ d.prefixRemainingList p, k l e ≤ Kinv) :
    ∀ l, ∑ e ∈ (d.angularSuccessor p v row).retainedList p, k l e ≤ K :=
  fun l => (hk l).trans hK

end PositiveDistanceData

namespace AngularStateData

theorem successor_budget (d : AngularStateData) {p K : ℕ} (hap : d.a ≤ p)
    (row : CellPath × CellPath) (k : Fin 2 → PolicyDescriptor → ℕ)
    (hk : ∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K) :
    ∀ l, ∑ e ∈ (d.successor p row).retainedList p, k l e ≤ K :=
  fun l => d.child_budget hap (k l) (hk l)

theorem far_recursive_cells (d : AngularStateData) {b : ℕ} (hab : d.a ≤ b)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    {row col : CellPath × CellPath} (hr : row ∈ d.children b) (hc : col ∈ d.children b)
    (hs : angularSeparated d.Q d.Q b row col) :
    ((d.distanceSuccessor b).atCells row.1 col.1).RecursiveCells ∧
      ((d.distanceSuccessor b).atCells row.2 col.2).RecursiveCells := by
  have hr' := d.children_lengths hab hX hY hr
  have hc' := d.children_lengths hab hX hY hc
  exact ⟨⟨hr'.1,hc'.1,hs.1⟩,⟨hr'.2,hc'.2,hs.2⟩⟩

theorem far_atCells_branchState (d : AngularStateData) (b : ℕ) (X Y : CellPath) :
    ((d.distanceSuccessor b).atCells X Y).branchState = .D b d.v (d.i+1) := rfl

theorem far_atCells_profile (d : AngularStateData) (b : ℕ) (X Y : CellPath) :
    ((d.distanceSuccessor b).atCells X Y).branchProfile = d.profile := rfl

end AngularStateData

end PlanarFalconer

end OAI
