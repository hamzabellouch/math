import OAI.Analysis.LipschitzHilbert.Geometry.FarSelectionGeometry

namespace OAI

/-! Width bounds at the local interval scale, derived from actual
non-removal rather than imposed as extra geometric assumptions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem local_selected_widths {ι κ : Type*} [Fintype κ]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle) (previous : Finset ι)
    (s r : ι) (hs : s ∈ previous) (hL : (R r).long ≤ (R s).long)
    (hinter : ((R s).carrier ∩ (R r).carrier).Nonempty)
    (hfar : 64*(R r).short < (R r).long*dist ((R s).axes 0) ((R r).axes 0))
    (hnot : ¬maximalBlocked e R selectionDilation (by norm_num) selectionThreshold previous r)
    (l θ : ℝ) (hl : 0 ≤ l) (hsize : (R r).long ≤ 16*l)
    (hangle : dist ((R s).axes 0) ((R r).axes 0) ≤ 2*θ) :
    (R s).short ≤ θ*l ∧ (R r).short ≤ θ*l := by
  have href := far_selected_reference_width e R previous s r hs hL hinter hfar hnot
  have hprod := mul_le_mul hsize hangle dist_nonneg (by linarith : 0 ≤ 16*l)
  constructor <;> nlinarith [(R s).short_pos,(R r).short_pos]

end LipschitzHilbert

end

end OAI
