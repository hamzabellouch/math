import OAI.Analysis.LipschitzHilbert.Geometry.NearRectangleSum

namespace OAI

/-! The near-angle selected overlap bound: maximal non-removal supplies
one point, and the explicit section estimate controls every near pair. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype κ]

theorem near_selected_overlap_bound (D : κ → Rectangle) (R : ι → Rectangle)
    (s previous : Finset ι) (r : ι) (i : κ) (A : ℝ) (hA : 0 ≤ A)
    (hs : s ⊆ previous) (η : ℝ≥0∞) (hη : ENNReal.ofReal (96*(A+1))*η ≤ 1)
    (hL : ∀ j ∈ s, (R r).long ≤ (R j).long)
    (hangle : ∀ j ∈ s, (R r).long * dist ((R j).axes 0) ((R r).axes 0) ≤ A*(R r).short)
    (htrans : ∀ j ∈ s, 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1|)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      (4*(A+1)+5) (by linarith) η previous r) :
    (∑ j ∈ s, volume ((R r).carrier ∩ (R j).carrier)) ≤ volume (R r).carrier := by
  classical
  let a := 4*(A+1)+5
  have ha : 0 < a := by dsimp [a]; linarith
  let g := rectangleCount (fun j => (R j).dilate a ha) previous
  let e := fun i => (D i).orthogonalCoordinates
  have hpoint : ∃ x ∈ (R r).carrier, positiveAuxiliary e g x ≤ η := by
    by_contra hn
    push Not at hn
    apply hnot
    exact hn
  obtain ⟨x,hx,hvalue⟩ := hpoint
  have hnear := near_intersection_sum_le_auxiliary D R s (R r) i A hA hL hangle htrans x hx
  have hm := positiveAuxiliary_mono e
    (rectangleCount_mono (fun j => (R j).dilate a ha) hs) x
  calc
    _ ≤ ENNReal.ofReal (96*(A+1))*volume (R r).carrier *
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a ha) s) x := hnear
    _ ≤ ENNReal.ofReal (96*(A+1))*volume (R r).carrier * η :=
      mul_le_mul' le_rfl (hm.trans hvalue)
    _ = (ENNReal.ofReal (96*(A+1))*η)*volume (R r).carrier := by ring
    _ ≤ 1*volume (R r).carrier := mul_le_mul' hη le_rfl
    _ = _ := one_mul _

end LipschitzHilbert

end

end OAI
