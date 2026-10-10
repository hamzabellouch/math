import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]

def idealWords (v : A) : Set A := { z | ∃ x y : A, z = x * v * y }
def idealSpan (v : A) : Submodule ℂ A := Submodule.span ℂ (idealWords v)

lemma idealSpan_word (v x y : A) : x * v * y ∈ idealSpan v :=
  Submodule.subset_span ⟨x, y, rfl⟩

lemma idealSpan_left {v z : A} (hz : z ∈ idealSpan v) (a : A) : a * z ∈ idealSpan v := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, y, rfl⟩ := hz
    simpa only [mul_assoc] using idealSpan_word v (a * x) y
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [mul_add] using (idealSpan v).add_mem ihx ihy
  | smul c x hx ih => simpa only [mul_smul_comm] using (idealSpan v).smul_mem c ih

lemma idealSpan_right {v z : A} (hz : z ∈ idealSpan v) (a : A) : z * a ∈ idealSpan v := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, y, rfl⟩ := hz
    simpa only [mul_assoc] using idealSpan_word v x (y * a)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [add_mul] using (idealSpan v).add_mem ihx ihy
  | smul c x hx ih => simpa only [smul_mul_assoc] using (idealSpan v).smul_mem c ih

lemma idealSpan_star {v z : A} (hv : IsSelfAdjoint v) (hz : z ∈ idealSpan v) :
    star z ∈ idealSpan v := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, y, rfl⟩ := hz
    simpa only [star_mul, hv.star_eq, mul_assoc] using idealSpan_word v (star y) (star x)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [star_add] using (idealSpan v).add_mem ihx ihy
  | smul c x hx ih => simpa only [star_smul] using (idealSpan v).smul_mem (star c) ih

def idealAlgebra (v : A) (hv : IsSelfAdjoint v) : NonUnitalStarSubalgebra ℂ A where
  carrier := idealSpan v
  zero_mem' := (idealSpan v).zero_mem
  add_mem' := (idealSpan v).add_mem
  smul_mem' := fun c _ hz => (idealSpan v).smul_mem c hz
  mul_mem' := fun _ hy => idealSpan_left hy _
  star_mem' := idealSpan_star hv

def closedIdeal (v : A) (hv : IsSelfAdjoint v) : NonUnitalStarSubalgebra ℂ A :=
  (idealAlgebra v hv).topologicalClosure

lemma closedIdeal_closed (v : A) (hv : IsSelfAdjoint v) :
    IsClosed (closedIdeal v hv : Set A) := isClosed_closure

instance closedIdeal_complete (v : A) (hv : IsSelfAdjoint v) :
    CompleteSpace (closedIdeal v hv) := (closedIdeal_closed v hv).completeSpace_coe

lemma closedIdeal_word (v : A) (hv : IsSelfAdjoint v) (x y : A) :
    x * v * y ∈ closedIdeal v hv := subset_closure (idealSpan_word v x y)

lemma self_mem_closedIdeal (v : A) (hv : IsSelfAdjoint v) : v ∈ closedIdeal v hv := by
  simpa using closedIdeal_word v hv 1 1

lemma closedIdeal_left {v z : A} (hv : IsSelfAdjoint v) (hz : z ∈ closedIdeal v hv) (a : A) :
    a * z ∈ closedIdeal v hv := by
  refine (closedIdeal_closed v hv).preimage (continuous_const.mul continuous_id)
    |>.closure_subset_iff.mpr (fun x hx => subset_closure (idealSpan_left hx a)) hz

lemma closedIdeal_right {v z : A} (hv : IsSelfAdjoint v) (hz : z ∈ closedIdeal v hv) (a : A) :
    z * a ∈ closedIdeal v hv := by
  refine (closedIdeal_closed v hv).preimage (continuous_id.mul continuous_const)
    |>.closure_subset_iff.mpr (fun x hx => subset_closure (idealSpan_right hx a)) hz

end MainGap

end

end OAI
