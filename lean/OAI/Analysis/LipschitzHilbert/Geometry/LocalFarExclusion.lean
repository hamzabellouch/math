import OAI.Analysis.LipschitzHilbert.Geometry.FarSlabExclusion
import OAI.Analysis.LipschitzHilbert.Estimates.LocalSelectedWidths

namespace OAI

/-! The long-overlap exclusion with its local width hypotheses discharged
by the actual reference rectangle and maximal non-removal. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem local_far_exclusion {ι : Type*} {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (s previous : Finset ι) (r ρ : ι) (hs : s ⊆ previous)
    (hρ : ρ ∈ previous) (hLref : (R r).long ≤ (R ρ).long)
    (hinter : ((R ρ).carrier ∩ (R r).carrier).Nonempty)
    (hfar : 64*(R r).short < (R r).long*dist ((R ρ).axes 0) ((R r).axes 0))
    (c l θ : ℝ) (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, 8*l ≤ (R j).long) (hTlong : (R r).long ≤ l)
    (hRangle : ∀ j ∈ s, dist ((R ρ).axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist ((R ρ).axes 0) ((R j).axes 0))
    (hTangle : dist ((R ρ).axes 0) ((R r).axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ (R ρ).stripSlab c l).Nonempty)
    (hT : ((R r).carrier ∩ (R ρ).stripSlab c (4*l)).Nonempty)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ s, volume ((R j).carrier ∩ (R ρ).stripSlab c l)) <
      volume ((R ρ).stripSlab c l) := by
  have hw := local_selected_widths (fun i => (D i).orthogonalCoordinates) R previous ρ r
    hρ hLref hinter hfar hnot l θ hl.le (by linarith) hTangle
  exact far_slab_selected_bound D hD R s previous r hs (R ρ) c l θ hl hθ hθsmall
    hRlong hTlong hw.1 hw.2 hRangle hRlower hTangle hR hT hnot

end LipschitzHilbert

end

end OAI
