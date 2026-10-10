import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferencePermutation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceWeightedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanEnergySum

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkDiagonalSourceFibreReindex
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryGiantOriginalMeanFactorization (Choices choicesPairSum)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

def diagonalWeight (outside : List ℕ) (a : SelectedNonbulkSample C l) (v : ℤ)
    (u : SelectedBulkSample C l) (P Q : ℤ) : ℂ :=
  HistoryDiagonalSmallOriginalMean.smallMultiplier C outside (fibreAssignment C a u) v P Q

theorem weightedMixedFibreMean_identity (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (v : ℤ) (c e : Choices (l:=l) C) :
    weightedMixedFibreMean C outside (Equiv.refl _) a v v c e (diagonalWeight C outside a v) =
      (selectedBulkPrior C l).cmean (fun u =>
        HistoryDiagonalSmallOriginalMean.originalMixedMean C outside
          (fibreAssignment C a u) (fibreAssignment C a u) v v c e) := by
  unfold weightedMixedFibreMean weightedFibreTerm
  simp only [permute_fibreAssignment,Equiv.refl_apply]
  rfl

def diagonalFibreMeanComplex (spectator : PrimeSource) : ℂ :=
  (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
    (selectedNonbulkPrior C l).cmean (fun a =>
      ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
        choicesPairSum C (fun c e =>
          weightedMixedFibreMean C (spectatorList spectator ds) (Equiv.refl _) a v.val v.val c e
            (diagonalWeight C (spectatorList spectator ds) a v.val))))

private theorem cmean_root_choices {A R : Type*} [Fintype A] [Fintype R]
    (μ : FinitePrior A) (F : A → R → Choices (l:=l) C → Choices (l:=l) C → ℂ) :
    μ.cmean (fun a => ∑ v, choicesPairSum C (F a v)) =
      ∑ v, choicesPairSum C (fun c e => μ.cmean (fun a => F a v c e)) := by
  simp only [choicesPairSum,FinitePrior.cmean_sum,FinitePrior.cmean_mul_left]

theorem selectedDiagonalSingleEnergy_eq_fibres (spectator : PrimeSource) :
    C.selectedDiagonalSingleEnergy spectator (bulkSize k L/2) C.scale l =
      (diagonalFibreMeanComplex (l:=l) C spectator).re := by
  rw [InitialSourceChoice.selectedDiagonalSingleEnergy,
    HistoryDiagonalSmallOriginalMean.diagonalSingleEnergy_eq_originalMean]
  apply congrArg Complex.re
  apply congrArg (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
  funext ds
  rw [selected_source_cmean_disintegration C l]
  apply congrArg (selectedNonbulkPrior C l).cmean
  funext a
  rw [cmean_root_choices C]
  apply Finset.sum_congr rfl
  intro v hv
  apply congrArg (choicesPairSum C)
  funext c e
  exact (weightedMixedFibreMean_identity C (spectatorList spectator ds) a v.val c e).symm

end Ostmann.Arithmetic.HistoryBulkDiagonalSourceFibreReindex

end

end OAI
