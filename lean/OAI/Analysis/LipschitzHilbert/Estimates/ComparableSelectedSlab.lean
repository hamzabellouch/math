import OAI.Analysis.LipschitzHilbert.Geometry.FarSlabExclusion
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleLastSelected
import OAI.Analysis.LipschitzHilbert.Estimates.LocalSelectedWidths

namespace OAI

/-! A comparable-length subfamily of an actual selection run has bounded
mass in a local strip. The required width bounds follow from non-removal. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem comparable_selected_slab {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (previous stock : Finset ι) (selected : List ι)
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    (s : Finset ι) (hsub : s ⊆ selected.toFinset) (ρ : ι) (hρ : ρ ∈ previous)
    (c l θ : ℝ) (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hsize : ∀ j ∈ s, l ≤ (R j).long ∧ (R j).long ≤ 16*l)
    (hLref : ∀ j ∈ s, (R j).long ≤ (R ρ).long)
    (hinter : ∀ j ∈ s, ((R ρ).carrier ∩ (R j).carrier).Nonempty)
    (hfar : ∀ j ∈ s, 64*(R j).short < (R j).long*dist ((R ρ).axes 0) ((R j).axes 0))
    (hangle : ∀ j ∈ s, dist ((R ρ).axes 0) ((R j).axes 0) ≤ 2*θ)
    (hlower : ∀ j ∈ s, θ/2 ≤ dist ((R ρ).axes 0) ((R j).axes 0))
    (hmeet : ∀ j ∈ s, ((R j).carrier ∩ (R ρ).stripSlab c l).Nonempty) :
    (∑ j ∈ s, volume ((R j).carrier ∩ (R ρ).stripSlab c l)) ≤
      2*volume ((R ρ).stripSlab c l) := by
  by_cases hs : s.Nonempty
  · obtain ⟨r,hr,p,hprev,herase,hnot⟩ := hrun.last_selected_witness s hs hsub
    have hwidth := local_selected_widths (fun i => (D i).orthogonalCoordinates) R p ρ r
      (hprev hρ) (hLref r hr) (hinter r hr) (hfar r hr) hnot l θ hl.le (hsize r hr).2 (hangle r hr)
    have hmeet4 : ((R r).carrier ∩ (R ρ).stripSlab c (4*l)).Nonempty := by
      obtain ⟨x,hxr,hxs⟩ := hmeet r hr
      have hh := ((R ρ).mem_stripSlab c l x).mp hxs
      exact ⟨x,hxr,((R ρ).mem_stripSlab c (4*l) x).mpr ⟨by linarith [hh.1],hh.2⟩⟩
    have hbound := comparable_slab_selected_bound D hD R (s.erase r) p r herase (R ρ) c l θ
      hl hθ hθsmall (fun j hj => (hsize j (Finset.mem_of_mem_erase hj)).1) (hsize r hr).2
      hwidth.1 hwidth.2 (fun j hj => hangle j (Finset.mem_of_mem_erase hj))
      (fun j hj => hlower j (Finset.mem_of_mem_erase hj)) (hangle r hr)
      (fun j hj => hmeet j (Finset.mem_of_mem_erase hj)) hmeet4 hnot
    calc
      _ = (∑ j ∈ s.erase r, volume ((R j).carrier ∩ (R ρ).stripSlab c l))+
          volume ((R r).carrier ∩ (R ρ).stripSlab c l) := (Finset.sum_erase_add _ _ hr).symm
      _ ≤ volume ((R ρ).stripSlab c l)+volume ((R ρ).stripSlab c l) :=
        add_le_add hbound.le (measure_mono inter_subset_right)
      _ = _ := by ring
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

end LipschitzHilbert

end

end OAI
