import OAI.Probability.InvariantIsing.Haar.RotationMatrix
import Mathlib.Data.List.Induction

namespace OAI

/-! Even nonzero reflection factorizations of special orthogonal matrices. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma rotationMatrix_list_prod {N : ℕ} (l : List (Rotation N)) :
    rotationMatrix l.prod = (l.map rotationMatrix).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.prod_cons,List.map_cons,rotationMatrix_mul,ih]

lemma reflectionList_remove_zero {N : ℕ} (l : List (EuclideanSpace ℝ (Fin N))) :
    ((l.filter (fun v => v ≠ 0)).map hyperplaneReflection).prod =
      (l.map hyperplaneReflection).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [ne_eq,decide_not] at ih
    by_cases ha : a = 0
    · simp [ha,ih]
    · simp [ha,ih]

lemma reflectionList_det {N : ℕ} (l : List (EuclideanSpace ℝ (Fin N)))
    (hl : ∀ v ∈ l, v ≠ 0) :
    (rotationMatrix ((l.map hyperplaneReflection).prod)).det = (-1 : ℝ)^l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have htail : ∀ v ∈ l, v ≠ 0 := fun v hv => hl v (by simp [hv])
    simp only [List.map_cons,List.prod_cons,rotationMatrix_mul,Matrix.det_mul,
      rotationMatrix_reflection_det a ha,ih htail,List.length_cons,pow_succ]
    ring

lemma specialRotation_even_reflections {N : ℕ} (U : SpecialOrthogonal N) :
    ∃ l : List (EuclideanSpace ℝ (Fin N)),
      (∀ v ∈ l, v ≠ 0) ∧ Even l.length ∧
      specialRotation U = (l.map hyperplaneReflection).prod := by
  obtain ⟨l,_,hl⟩ := (specialRotation U).reflections_generate_dim
  let l' := l.filter (fun v => v ≠ 0)
  have hnonzero : ∀ v ∈ l', v ≠ 0 := by
    intro v hv
    exact of_decide_eq_true (List.mem_filter.mp hv).2
  have heq : specialRotation U = (l'.map hyperplaneReflection).prod := by
    rw [reflectionList_remove_zero]
    exact hl
  have hdet : (-1 : ℝ)^l'.length = 1 := by
    rw [← reflectionList_det l' hnonzero,← heq,rotationMatrix_specialRotation]
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).2
  exact ⟨l',hnonzero,(neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hdet,heq⟩

end InvariantIsing

end

end OAI
