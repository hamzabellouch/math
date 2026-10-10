import OAI.GroupTheory.PolycyclicRecognition.Geometry.ListBarBoundaryOperators
import Mathlib.LinearAlgebra.Finsupp.Supported

namespace OAI

/-! # Degree control for the integral bar shuffle operators -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

def listBarGrade (n : ℕ) : Submodule ℤ (ListBarChain A) :=
  Finsupp.supported ℤ ℤ {v | v.length = n}

theorem listBarGrade_single (v : List A) (z : ℤ) :
    Finsupp.single v z ∈ listBarGrade v.length := Finsupp.single_mem_supported ℤ z rfl

theorem listBarPrepend_grade (a : A) {n : ℕ} {z : ListBarChain A}
    (hz : z ∈ listBarGrade n) : listBarPrepend a z ∈ listBarGrade (n + 1) := by
  have hm : listBarPrepend a z ∈ (listBarGrade n).map (listBarPrepend a) := ⟨z, hz, rfl⟩
  rw [listBarGrade, listBarPrepend, Finsupp.lmapDomain_supported] at hm
  apply Finsupp.supported_mono ?_ hm
  rintro _ ⟨v, hv, rfl⟩
  change (a :: v).length = n + 1
  simp only [List.length_cons, Set.mem_ofPred_eq] at hv ⊢
  rw [hv]

theorem listBarInsertValue_grade (a : A) (v : List A) :
    listBarInsertValue a v ∈ listBarGrade (v.length + 1) := by
  induction v with
  | nil => exact listBarGrade_single [a] 1
  | cons b v ih =>
    apply (listBarGrade _).sub_mem
    · exact listBarGrade_single (a :: b :: v) 1
    · simpa only [List.length_cons] using listBarPrepend_grade b ih

theorem listBarInsert_grade (a : A) {n : ℕ} {z : ListBarChain A}
    (hz : z ∈ listBarGrade n) : listBarInsert a z ∈ listBarGrade (n + 1) := by
  rw [listBarGrade, Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [listBarInsert_single]
    simpa only [Set.mem_ofPred_eq] using hv ▸ listBarInsertValue_grade a v
  | zero => simpa only [map_zero] using (listBarGrade (n + 1)).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (listBarGrade _).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using (listBarGrade _).smul_mem r hx

theorem listBarPairValue_grade (a b : A) (v : List A) :
    listBarPairValue a b v ∈ listBarGrade (v.length + 2) := by
  induction v with
  | nil => exact listBarGrade_single [a, b] 1
  | cons c v ih =>
    apply (listBarGrade _).add_mem
    · simpa only [List.length_cons, Nat.add_assoc] using
        listBarPrepend_grade a (listBarInsertValue_grade b (c :: v))
    · simpa only [List.length_cons, Nat.add_comm 1 2, Nat.add_assoc] using
        listBarPrepend_grade c ih

theorem listBarPair_grade (a b : A) {n : ℕ} {z : ListBarChain A}
    (hz : z ∈ listBarGrade n) : listBarPair a b z ∈ listBarGrade (n + 2) := by
  rw [listBarGrade, Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [listBarPair_single]
    simpa only [Set.mem_ofPred_eq] using hv ▸ listBarPairValue_grade a b v
  | zero => simpa only [map_zero] using (listBarGrade (n + 2)).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (listBarGrade _).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using (listBarGrade _).smul_mem r hx

end PolycyclicRecognition

end

end OAI
