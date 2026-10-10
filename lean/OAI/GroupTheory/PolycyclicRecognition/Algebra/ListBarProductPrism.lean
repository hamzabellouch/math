import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListBarProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListBarHomogeneous

namespace OAI

/-! # Degree-controlled additivity prisms in every bar coordinate -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

theorem listBarProduct_grade (v : List A) : listBarProduct v ∈ listBarGrade v.length := by
  induction v with
  | nil => exact listBarGrade_single [] 1
  | cons a v ih => exact listBarInsert_grade a ih

theorem listBarInsert_product_eq_zero_of_mem (a : A) (v : List A) (h : a ∈ v) :
    listBarInsert a (listBarProduct v) = 0 := by
  induction v with
  | nil => simp at h
  | cons b v ih =>
    rcases List.mem_cons.mp h with hab | hv
    · subst b
      exact listBarInsert_square_zero a (listBarProduct v)
    · rw [listBarProduct, listBarInsert_anticommute, ih hv, map_zero, neg_zero]

theorem listBarProduct_eq_zero_of_not_nodup (v : List A) (h : ¬v.Nodup) :
    listBarProduct v = 0 := by
  classical
  induction v with
  | nil => simp at h
  | cons a v ih =>
    by_cases ha : a ∈ v
    · exact listBarInsert_product_eq_zero_of_mem a v ha
    · have hv : ¬v.Nodup := fun hv => h (List.nodup_cons.mpr ⟨ha, hv⟩)
      rw [listBarProduct, ih hv, map_zero]

def listBarProductPrism (a b : A) (suffix : List A) : List A → ListBarChain A
  | [] => -listBarPair a b (listBarProduct suffix)
  | c :: pre => -listBarInsert c (listBarProductPrism a b suffix pre)

theorem listBarProductPrism_grade (a b : A) (suffix pre : List A) :
    listBarProductPrism a b suffix pre ∈ listBarGrade (pre.length + suffix.length + 2) := by
  induction pre with
  | nil =>
    simpa only [listBarProductPrism, List.length_nil, zero_add] using
      (listBarGrade _).neg_mem (listBarPair_grade a b (listBarProduct_grade suffix))
  | cons c pre ih =>
    have hh := (listBarGrade _).neg_mem (listBarInsert_grade c ih)
    have he : pre.length + suffix.length + 2 + 1 = (pre.length + 1) + suffix.length + 2 := by omega
    simpa only [listBarProductPrism, List.length_cons, he] using hh

theorem listBarProductPrism_boundary [CommSemigroup A] (a b : A) (suffix pre : List A) :
    listBarBoundary (listBarProductPrism a b suffix pre) =
      listBarProduct (pre ++ (a * b) :: suffix) - listBarProduct (pre ++ a :: suffix) -
        listBarProduct (pre ++ b :: suffix) := by
  induction pre with
  | nil =>
    rw [listBarProductPrism, map_neg, listBarBoundary_pair, listBarProduct_cycle, map_zero]
    simp only [List.nil_append, listBarProduct]
    abel
  | cons c pre ih =>
    rw [listBarProductPrism, map_neg, listBarBoundary_insert, neg_neg, ih]
    simp only [List.cons_append, listBarProduct, map_sub]

end PolycyclicRecognition

end

end OAI
