import OAI.Analysis.LipschitzHilbert.Estimates.ComparableSelectedSlab
import OAI.Analysis.LipschitzHilbert.Geometry.LocalFarExclusion
import OAI.Analysis.LipschitzHilbert.Trees.StripMassOperations

namespace OAI

/-! A finite far family inside an actual selection run. These data will
be obtained from the projected-popularity grouping; the local estimates
below use no further geometric assumptions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert

structure SelectedFarFamily (ι : Type*) [DecidableEq ι] where
  n : ℕ
  directions : Fin n → Rectangle
  direction_net : ∀ T : Rectangle, ∃ i, dist ((directions i).axes 0) (T.axes 1) < 1/4
  rectangles : ι → Rectangle
  previous : Finset ι
  stock : Finset ι
  selected : List ι
  run : RectangleCoverRun rectangles
    (maximalBlocked (fun i => (directions i).orthogonalCoordinates) rectangles
      selectionDilation (by norm_num) selectionThreshold) previous stock selected
  members : Finset ι
  members_selected : members ⊆ selected.toFinset
  reference : ι
  reference_previous : reference ∈ previous
  angle : ℝ
  angle_pos : 0 < angle
  angle_small : angle ≤ 1/20
  lengths : ∀ j ∈ members, (rectangles j).long ≤ (rectangles reference).long
  intersects : ∀ j ∈ members, ((rectangles reference).carrier ∩ (rectangles j).carrier).Nonempty
  far : ∀ j ∈ members, 64*(rectangles j).short <
    (rectangles j).long*dist ((rectangles reference).axes 0) ((rectangles j).axes 0)
  angle_upper : ∀ j ∈ members, dist ((rectangles reference).axes 0) ((rectangles j).axes 0) ≤ 2*angle
  angle_lower : ∀ j ∈ members, angle/2 ≤ dist ((rectangles reference).axes 0) ((rectangles j).axes 0)

namespace SelectedFarFamily
variable {ι : Type*} [DecidableEq ι]

abbrev refRect (F : SelectedFarFamily ι) : Rectangle := F.rectangles F.reference

def longMembers (F : SelectedFarFamily ι) (l : ℝ) : Finset ι :=
  F.members.filter (fun j => 8*l ≤ (F.rectangles j).long)

def comparableMembers (F : SelectedFarFamily ι) (l : ℝ) : Finset ι :=
  F.members.filter (fun j => l ≤ (F.rectangles j).long ∧ (F.rectangles j).long ≤ 16*l)

theorem comparable_mass (F : SelectedFarFamily ι) (c l : ℝ) (hl : 0 < l) :
    stripMass F.rectangles (F.comparableMembers l) F.refRect c l ≤
      2*volume (F.refRect.stripSlab c l) := by
  let t := (F.comparableMembers l).filter
    (fun j => ((F.rectangles j).carrier ∩ F.refRect.stripSlab c l).Nonempty)
  have ht (j : ι) (hj : j ∈ t) : j ∈ F.members :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
  have hb := comparable_selected_slab F.directions F.direction_net F.rectangles
    F.previous F.stock F.selected F.run t (fun j hj => F.members_selected (ht j hj))
    F.reference F.reference_previous c l F.angle hl F.angle_pos F.angle_small
    (fun j hj => (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2)
    (fun j hj => F.lengths j (ht j hj)) (fun j hj => F.intersects j (ht j hj))
    (fun j hj => F.far j (ht j hj)) (fun j hj => F.angle_upper j (ht j hj))
    (fun j hj => F.angle_lower j (ht j hj)) (fun j hj => (Finset.mem_filter.mp hj).2)
  change stripMass F.rectangles t F.refRect c l ≤ _ at hb
  simpa only [t,stripMass_filter_meets] using hb

/-- A strip with large long-rectangle mass cannot meet a shorter selected
rectangle, even in its fourfold enlargement. -/
theorem short_absent (F : SelectedFarFamily ι) (c l : ℝ) (hl : 0 < l)
    (hdense : volume (F.refRect.stripSlab c l) ≤
      stripMass F.rectangles (F.longMembers l) F.refRect c l)
    (r : ι) (hr : r ∈ F.members) (hrshort : (F.rectangles r).long < l) :
    ¬((F.rectangles r).carrier ∩ F.refRect.stripSlab c (4*l)).Nonempty := by
  intro hmeet
  obtain ⟨p,hprev,hbefore,hnot⟩ := F.run.selected_previous_witness r
    (List.mem_toFinset.mp (F.members_selected hr))
  let t := (F.longMembers l).filter
    (fun j => ((F.rectangles j).carrier ∩ F.refRect.stripSlab c l).Nonempty)
  have ht (j : ι) (hj : j ∈ t) : j ∈ F.members ∧ 8*l ≤ (F.rectangles j).long :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hj).1
  have htp : t ⊆ p := by
    intro j hj
    exact hbefore j (List.mem_toFinset.mp (F.members_selected (ht j hj).1)) (by linarith [(ht j hj).2])
  have hb := local_far_exclusion F.directions F.direction_net F.rectangles t p r F.reference
    htp (hprev F.reference_previous) (F.lengths r hr) (F.intersects r hr) (F.far r hr)
    c l F.angle hl F.angle_pos F.angle_small (fun j hj => (ht j hj).2) hrshort.le
    (fun j hj => F.angle_upper j (ht j hj).1) (fun j hj => F.angle_lower j (ht j hj).1)
    (F.angle_upper r hr) (fun j hj => (Finset.mem_filter.mp hj).2) hmeet hnot
  change stripMass F.rectangles t F.refRect c l < _ at hb
  rw [show t = (F.longMembers l).filter
      (fun j => ((F.rectangles j).carrier ∩ F.refRect.stripSlab c l).Nonempty) from rfl,
    stripMass_filter_meets] at hb
  exact (not_lt_of_ge hdense) hb

end SelectedFarFamily
end LipschitzHilbert

end

end OAI
