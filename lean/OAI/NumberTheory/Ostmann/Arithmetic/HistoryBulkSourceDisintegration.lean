import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegrationMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegrationPermutation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegrationSelectedDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkSourceDisintegration
open Construction Conclusion
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)

theorem selectedSourceEquiv_mass
    (x : SourceAssignment C.sources (SelectedTemplate k L l)) :
    (assignmentPrior C.sources (SelectedTemplate k L l)).mass x =
      (selectedNonbulkPrior C l).mass (selectedSourceEquiv C l x).1 *
      (selectedBulkPrior C l).mass (selectedSourceEquiv C l x).2 :=
  coordinateEquiv_mass _ _ _ _ _ x

theorem selected_source_cmean_disintegration
    (F : SourceAssignment C.sources (SelectedTemplate k L l) → ℂ) :
    (assignmentPrior C.sources (SelectedTemplate k L l)).cmean F =
      (selectedNonbulkPrior C l).cmean (fun a => (selectedBulkPrior C l).cmean (fun y =>
        F ((selectedSourceEquiv C l).symm (a,y)))) :=
  source_cmean_disintegration _ _ _ _ _ F

theorem selected_coordinates_cmean
    (F : SelectedNonbulkSample C l × SelectedBulkSample C l → ℂ) :
    (assignmentPrior C.sources (SelectedTemplate k L l)).cmean (fun x => F (selectedSourceEquiv C l x)) =
      (selectedNonbulkPrior C l).cmean (fun a => (selectedBulkPrior C l).cmean (fun y => F (a,y))) :=
  coordinateEquiv_cmean _ _ _ _ _ F

theorem selectedSourceEquiv_permutation
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (x : SourceAssignment C.sources (SelectedTemplate k L l)) :
    selectedSourceEquiv C l
      (sourceAssignmentPermutation C.sources (SelectedTemplate k L l)
        (selectedLeafPermutation C l σ) (selectedLeafPermutation_source C l σ) x) =
      ((selectedSourceEquiv C l x).1,fun u => (selectedSourceEquiv C l x).2 (σ u)) := by
  apply coordinateEquiv_permutation
  · intro i
    exact leafBulkPermutation_apply_nonbulk (2*(bulkSize k L/2)) k l σ i.val i.property
  · intro u
    exact leafBulkPermutation_apply_leaf (2*(bulkSize k L/2)) k l σ u

theorem selectedSourceEquiv_symm_permutation
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (a : SelectedNonbulkSample C l) (y : SelectedBulkSample C l) :
    sourceAssignmentPermutation C.sources (SelectedTemplate k L l)
      (selectedLeafPermutation C l σ) (selectedLeafPermutation_source C l σ)
      ((selectedSourceEquiv C l).symm (a,y)) =
    (selectedSourceEquiv C l).symm (a,fun u => y (σ u)) := by
  apply (selectedSourceEquiv C l).injective
  rw [selectedSourceEquiv_permutation,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

end Ostmann.Arithmetic.HistoryBulkSourceDisintegration

end

end OAI
