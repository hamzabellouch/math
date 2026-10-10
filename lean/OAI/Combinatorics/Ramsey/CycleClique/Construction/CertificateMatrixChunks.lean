import OAI.Combinatorics.Ramsey.CycleClique.Construction.TemplateMatrix
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RequiredCertificates

namespace OAI

/-! Matrix folds can be normalized in short, separately checked chunks. -/

namespace CycleClique.Construction
theorem templateMatrix_append_apply {n : ℕ}
    (A B : List (TemplateData (Fin n))) (i j : Fin n) :
    templateMatrix (A ++ B) i j = templateMatrix A i j ∪ templateMatrix B i j := by
  induction A with
  | nil => simp only [List.nil_append, templateMatrix, Finset.empty_union]
  | cons T A ih =>
    simp only [List.cons_append, templateMatrix, ih, Finset.union_assoc]

theorem requiredMatrix_append_apply {n : ℕ} (k : ℕ)
    (A B : List (RequiredPathData (Fin n))) (i j : Fin n) :
    requiredMatrix k (A ++ B) i j = requiredMatrix k A i j ∪ requiredMatrix k B i j := by
  induction A with
  | nil => simp only [List.nil_append, requiredMatrix, Finset.empty_union]
  | cons p A ih =>
    simp only [List.cons_append, requiredMatrix, ih, Finset.union_assoc]

theorem templateMatrix_append {n : ℕ}
    (A B : List (TemplateData (Fin n))) :
    templateMatrix (A ++ B) = fun i j => templateMatrix A i j ∪ templateMatrix B i j := by
  funext i j
  exact templateMatrix_append_apply A B i j

theorem requiredMatrix_append {n : ℕ} (k : ℕ)
    (A B : List (RequiredPathData (Fin n))) :
    requiredMatrix k (A ++ B) =
      fun i j => requiredMatrix k A i j ∪ requiredMatrix k B i j := by
  funext i j
  exact requiredMatrix_append_apply k A B i j

end CycleClique.Construction

end OAI
