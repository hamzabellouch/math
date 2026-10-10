import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegrationDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceDisintegration
open Construction Conclusion
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

abbrev SelectedTemplate (k : ℕ) (L : ℝ) (l : ℕ) :=
  Template.current (Template.initial (2*(bulkSize k L/2)) k) l

theorem selected_bulk_source (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)
    (i : BulkPosition (SelectedTemplate k L l)) :
    C.sources ((SelectedTemplate k L l).get i.val).origin = C.bulk := by
  unfold InitialSourceChoice.sources NominalCenterArray.sources
  exact current_bulk_source (bulkSize k L/2) k l C.bulk
    (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) i

abbrev SelectedNonbulkSample (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ) :=
  NonbulkSample C.sources (SelectedTemplate k L l)

abbrev SelectedBulkSample (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ) :=
  (Fin (2^l) × Fin (2*(bulkSize k L/2))) → C.bulk.Sample

def selectedNonbulkPrior (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ) :
    FinitePrior (SelectedNonbulkSample C l) := nonbulkPrior C.sources (SelectedTemplate k L l)

def selectedBulkPrior (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ) :
    FinitePrior (SelectedBulkSample C l) :=
  bulkPrior C.bulk (Fin (2^l) × Fin (2*(bulkSize k L/2)))

def selectedSourceEquiv (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ) :
    SourceAssignment C.sources (SelectedTemplate k L l) ≃
      SelectedNonbulkSample C l × SelectedBulkSample C l :=
  coordinateEquiv C.sources (SelectedTemplate k L l) C.bulk (selected_bulk_source C l)
    (currentBulkPositionEquiv (2*(bulkSize k L/2)) k l)

@[simp] theorem selectedSourceEquiv_nonbulk (C : InitialSourceChoice d Bs BD Bz k L E)
    (l : ℕ) (x : SourceAssignment C.sources (SelectedTemplate k L l))
    (i : NonbulkPosition (SelectedTemplate k L l)) :
    (selectedSourceEquiv C l x).1 i = x i.val := rfl

@[simp] theorem selectedSourceEquiv_bulk_val (C : InitialSourceChoice d Bs BD Bz k L E)
    (l : ℕ) (x : SourceAssignment C.sources (SelectedTemplate k L l))
    (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    ((selectedSourceEquiv C l x).2 u).val =
      (x ((currentBulkPositionEquiv (2*(bulkSize k L/2)) k l).symm u).val).val :=
  coordinateEquiv_bulk_val _ _ _ _ _ x u

end Ostmann.Arithmetic.HistoryBulkSourceDisintegration

end

end OAI
