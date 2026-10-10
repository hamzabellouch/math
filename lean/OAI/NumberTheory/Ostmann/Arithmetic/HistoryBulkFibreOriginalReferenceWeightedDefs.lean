import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceTermDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Seed Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)
variable (J : SelectedBulkSample C l → ℤ → ℤ → ℂ)

def weightedFibreTerm (y : SelectedBulkSample C l) (P Q : ℤ) : ℂ :=
  sourceIntegrand d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) outside l
    (sourceState C.sources _ (fibreAssignment C a y) s)
    (sourceState C.sources _ (permuteAssignment C σ (fibreAssignment C a y)) t)
    c e (J y) (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.bulkBin C.spectatorBin C.giantCenter P Q

theorem weightedFibreTerm_eq_mul (y : SelectedBulkSample C l) (P Q : ℤ) :
    weightedFibreTerm C outside σ a s t c e J y P Q =
      J y P Q * fibreTerm C outside σ a s t c e y P Q := by
  simp only [weightedFibreTerm,fibreTerm,sourceIntegrand,one_mul]

theorem weightedFibreTerm_ne_zero_supported (y : SelectedBulkSample C l) (P Q : ℤ)
    (h : weightedFibreTerm C outside σ a s t c e J y P Q ≠ 0) :
    FibreSupported C outside σ a s t c e y P Q := by
  rw [weightedFibreTerm_eq_mul] at h
  exact fibreTerm_ne_zero_supported C outside σ a s t c e y P Q (mul_ne_zero_iff.mp h).2

def weightedPrimeFibreMean : ℂ :=
  (selectedBulkPrior C l).cmean (fun y =>
    primeMean C.giant (weightedFibreTerm C outside σ a s t c e J y))

def weightedMixedFibreMean : ℂ :=
  (selectedBulkPrior C l).cmean (fun y =>
    mixedMean C.giantCenter C.giant (weightedFibreTerm C outside σ a s t c e J y))

theorem weightedPrimeFibreMean_eq_weighted :
    weightedPrimeFibreMean C outside σ a s t c e J =
      HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass (primeWeight C.giant)
        (fun y r => weightedFibreTerm C outside σ a s t c e J y
          (primeP C.giant r) (primeQ C.giant r)) := by
  simp only [weightedPrimeFibreMean,primeMean_eq_weighted,FinitePrior.cmean,
    HistoryBulkFibreReference.originalMean,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

theorem weightedMixedFibreMean_eq_weighted :
    weightedMixedFibreMean C outside σ a s t c e J =
      HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass
        (mixedWeight C.giantCenter C.giant)
        (fun y r => weightedFibreTerm C outside σ a s t c e J y
          (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r)) := by
  simp only [weightedMixedFibreMean,mixedMean_eq_weighted,FinitePrior.cmean,
    HistoryBulkFibreReference.originalMean,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
