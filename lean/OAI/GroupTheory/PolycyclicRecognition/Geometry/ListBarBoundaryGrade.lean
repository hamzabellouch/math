import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListBarCoordinates

namespace OAI

/-! # The list boundary preserves the ordinary homological grading -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type} [Mul A]

theorem listBarBoundaryValue_grade (v : List A) :
    listBarBoundaryValue v ∈ listBarGrade (v.length - 1) := by
  induction v with
  | nil => exact (listBarGrade 0).zero_mem
  | cons a v ih =>
    cases v with
    | nil => exact (listBarGrade 0).zero_mem
    | cons b v =>
      change listBarBoundaryValue (a :: b :: v) ∈ listBarGrade (v.length + 1)
      apply (listBarGrade _).sub_mem
      · apply (listBarGrade _).add_mem
        · exact (listBarGrade _).sub_mem (listBarGrade_single (b :: v) 1)
            (listBarGrade_single ((a * b) :: v) 1)
        · exact listBarPrepend_grade a (listBarGrade_single v 1)
      · apply listBarPrepend_grade a
        simpa only [List.length_cons, Nat.add_sub_cancel] using ih

theorem listBarBoundary_grade {n : ℕ} {z : ListBarChain A}
    (hz : z ∈ listBarGrade (n + 1)) : listBarBoundary z ∈ listBarGrade n := by
  rw [listBarGrade, Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [listBarBoundary_single]
    have hh := listBarBoundaryValue_grade v
    change v.length = n + 1 at hv
    simpa only [hv, Nat.add_sub_cancel] using hh
  | zero => simpa only [map_zero] using (listBarGrade n).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (listBarGrade _).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using (listBarGrade _).smul_mem r hx

end PolycyclicRecognition

end

end OAI
