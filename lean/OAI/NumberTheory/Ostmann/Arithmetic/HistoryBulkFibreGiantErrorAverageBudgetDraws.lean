import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageBudgetNested
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamilyRoots

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter HistoryGiantOriginalMeanFactorization
open HistoryBulkReferenceFrequencyFamily

theorem choices_sum_eq_source_cmean (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (F : HistoryChoices sources seed V l → ℂ) :
    (∑ c, (choicesMass sources seed V l c : ℂ)*F c) =
      (internalSourcePrior sources seed l).cmean (fun x =>
        ∑ f, F (assembleHistoryChoices sources seed V l f x)) := by
  rw [sum_choicesMass_eq_source_prior]
  simp only [FinitePrior.cmean, Finset.mul_sum]
  exact Finset.sum_comm

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

theorem choicesPairSum_eq_source_cmean
    (F : Choices (l:=l) C → Choices (l:=l) C → ℂ) :
    choicesPairSum C F =
      (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun x =>
        (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun y =>
          ∑ f, ∑ g, F
            (assembleHistoryChoices C.sources (Seed (k:=k) (L:=L))
              (frequencyBound Bs BD Bz k L) l f x)
            (assembleHistoryChoices C.sources (Seed (k:=k) (L:=L))
              (frequencyBound Bs BD Bz k L) l g y))) := by
  unfold choicesPairSum
  simp only [Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum]
  simp_rw [choices_sum_eq_source_cmean]
  simp only [FinitePrior.cmean_sum]

theorem root_choices_sum_eq_source_cmean
    (F : AllowedFrequency (frequencyBound Bs BD Bz k L) l →
      Choices (l:=l) C → Choices (l:=l) C → ℂ) :
    (∑ r, choicesPairSum C (F r)) =
      (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun x =>
        (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun y =>
          ∑ i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l,
            F i.1
              (assembleHistoryChoices C.sources (Seed (k:=k) (L:=L))
                (frequencyBound Bs BD Bz k L) l i.2.1 x)
              (assembleHistoryChoices C.sources (Seed (k:=k) (L:=L))
                (frequencyBound Bs BD Bz k L) l i.2.2 y))) := by
  simp only [RootFrequencyIndex, Fintype.sum_prod_type, choicesPairSum_eq_source_cmean,
    FinitePrior.cmean_sum]

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
