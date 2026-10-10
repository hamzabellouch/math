import OAI.Combinatorics.Crossing.DrawingDiskIsolation
import OAI.Combinatorics.Crossing.SortedMarkedParameters
import OAI.Combinatorics.Crossing.OrderedPassages

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

structure DrawingPassages (D : FiniteIntersectionDrawing m n) where
  radius : ℝ
  radius_pos : 0 < radius
  disks_disjoint : ∀ x y : DrawingMark D, x ≠ y →
    Disjoint (closedRoundDisk x.val radius) (closedRoundDisk y.val radius)
  count : BipartiteEdge m n → ℕ
  count_pos : ∀ e, 0 < count e
  node : ∀ e, Fin (count e+1) → unitInterval
  increasing : ∀ e, StrictMono (node e)
  first : ∀ e, node e 0=0
  last : ∀ e, node e (Fin.last (count e))=1
  node_range : ∀ e, Set.range (node e)=(D.edge e) ⁻¹' drawingMarks D
  passage : ∀ e i, DiskPassage (D.edge e) (D.edge e (node e i)) radius (node e i)
  separated : ∀ e i j, i < j → (passage e i).leave < (passage e j).enter
  visited_mark_on_edge : ∀ e (x : DrawingMark D) t,
    D.edge e t ∈ closedRoundDisk x.val radius → ∃ u, D.edge e u=x.val

theorem nonempty_drawingPassages (D : FiniteIntersectionDrawing m n) : Nonempty (DrawingPassages D) := by
  classical
  obtain ⟨δ,r,hδ,hr,hdisks,hvisits,hparam⟩ := drawing_disk_isolation D
  choose k hk τ hτ h0 h1 hR using (fun e => exists_sorted_drawing_parameters D e)
  have hnode (e : BipartiteEdge m n) (i : Fin (k e+1)) : D.edge e (τ e i) ∈ drawingMarks D := by
    change τ e i ∈ (D.edge e) ⁻¹' drawingMarks D
    rw [← hR e]
    exact ⟨i,rfl⟩
  have hex (e : BipartiteEdge m n) (i : Fin (k e+1)) :
      Nonempty (DiskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)) :=
    nonempty_diskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)
      (by simpa [squaredLength] using sq_pos_of_pos hr)
  let P (e : BipartiteEdge m n) (i : Fin (k e+1)) := Classical.choice (hex e i)
  have hlocal (e : BipartiteEdge m n) (i : Fin (k e+1)) (t : unitInterval)
      (ht : D.edge e t ∈ closedRoundDisk (D.edge e (τ e i)) r) :
      t ∈ parameterNeighborhood (τ e i) (δ e) := by
    obtain ⟨u,hu,hh⟩ := hvisits e ⟨D.edge e (τ e i),hnode e i⟩ t ht
    have he : u=τ e i := D.edge_injective e hu
    simpa [he] using hh
  have hsep (e : BipartiteEdge m n) (i j : Fin (k e+1)) (hij : i < j) :
      (P e i).leave < (P e j).enter := by
    apply diskPassage_separated (P e i) (P e j) (hτ e hij) (hδ e)
    · exact hparam e (τ e i) (τ e j) (hnode e i) (hnode e j) ((hτ e).injective.ne (ne_of_lt hij))
    · exact hlocal e i _ (P e i).leave_mem
    · exact hlocal e j _ (P e j).enter_mem
  exact ⟨{
    radius := r
    radius_pos := hr
    disks_disjoint := hdisks
    count := k
    count_pos := hk
    node := τ
    increasing := hτ
    first := h0
    last := h1
    node_range := hR
    passage := P
    separated := hsep
    visited_mark_on_edge := fun e x t ht => by
      obtain ⟨u,hu,_⟩ := hvisits e x t ht
      exact ⟨u,hu⟩ }⟩

end Zarankiewicz

end

end OAI
