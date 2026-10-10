import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryGiantReferenceMean
open HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Seed Current Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

@[simp] theorem fibreAssignment_mass (a : SelectedNonbulkSample C l) (y : SelectedBulkSample C l) :
    (assignmentPrior C.sources (SelectedTemplate k L l)).mass (fibreAssignment C a y) =
      (selectedNonbulkPrior C l).mass a * (selectedBulkPrior C l).mass y := by
  simpa only [fibreAssignment,Equiv.apply_symm_apply] using
    selectedSourceEquiv_mass C l ((selectedSourceEquiv C l).symm (a,y))

@[simp] theorem fibreAssignment_nonbulk (a : SelectedNonbulkSample C l) (y : SelectedBulkSample C l)
    (i : NonbulkPosition (SelectedTemplate k L l)) : fibreAssignment C a y i.val = a i := by
  simpa only [fibreAssignment,Equiv.apply_symm_apply] using
    (selectedSourceEquiv_nonbulk C l ((selectedSourceEquiv C l).symm (a,y)) i).symm

theorem fibreAssignment_nonbulk_fixed (a : SelectedNonbulkSample C l)
    (y z : SelectedBulkSample C l) (i : Fin (SelectedTemplate k L l).length)
    (hi : ((SelectedTemplate k L l).get i).role ≠ .bulk) :
    (fibreAssignment C a y i).val = (fibreAssignment C a z i).val := by
  have hy := fibreAssignment_nonbulk C a y ⟨i,hi⟩
  have hz := fibreAssignment_nonbulk C a z ⟨i,hi⟩
  exact congrArg Subtype.val (hy.trans hz.symm)

variable (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)

theorem primeFibreMean_eq_weighted :
    primeFibreMean C outside σ a s t c e =
      HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass (primeWeight C.giant)
        (fun y r => fibreTerm C outside σ a s t c e y (primeP C.giant r) (primeQ C.giant r)) := by
  simp only [primeFibreMean,primeMean_eq_weighted,FinitePrior.cmean,
    HistoryBulkFibreReference.originalMean,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

theorem mixedFibreMean_eq_weighted :
    mixedFibreMean C outside σ a s t c e =
      HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass
        (mixedWeight C.giantCenter C.giant)
        (fun y r => fibreTerm C outside σ a s t c e y
          (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r)) := by
  simp only [mixedFibreMean,mixedMean_eq_weighted,FinitePrior.cmean,
    HistoryBulkFibreReference.originalMean,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

theorem originalPrimeMean_disintegration :
    (assignmentPrior C.sources (SelectedTemplate k L l)).cmean (fun x =>
      HistoryGiantUncorrectedOriginalMean.originalPrimeMean C outside x (permuteAssignment C σ x) s t c e) =
    (selectedNonbulkPrior C l).cmean (fun a => primeFibreMean C outside σ a s t c e) := by
  exact selected_source_cmean_disintegration C l _

theorem originalMixedMean_disintegration :
    (assignmentPrior C.sources (SelectedTemplate k L l)).cmean (fun x =>
      HistoryGiantUncorrectedOriginalMean.originalMixedMean C outside x (permuteAssignment C σ x) s t c e) =
    (selectedNonbulkPrior C l).cmean (fun a => mixedFibreMean C outside σ a s t c e) := by
  exact selected_source_cmean_disintegration C l _

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
