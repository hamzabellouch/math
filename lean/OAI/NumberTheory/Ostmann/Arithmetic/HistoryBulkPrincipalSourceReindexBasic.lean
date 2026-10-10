import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanChoicesDefs
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesPair

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex
open Construction Conclusion CanonicalOccurrenceTransport
open HistoryGiantOriginalMeanFactorization
open scoped BigOperators
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)

theorem choicesPairSum_eq_frequency_sourceMean
    (F : Choices (l:=l) C → Choices (l:=l) C → ℂ) :
    choicesPairSum C F =
      ∑f : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
      ∑g : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
      (pairedInternalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).cmean
        (fun z=>F
          (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
            (frequencyBound Bs BD Bz k L) l f (fun i=>z (.inl i)))
          (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
            (frequencyBound Bs BD Bz k L) l g (fun i=>z (.inr i)))) := by
  simpa only [choicesPairSum,FinitePrior.cmean,Complex.ofReal_mul,mul_assoc] using
    sum_pair_choicesMass_eq_source_prior C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) l F

theorem sum_cmean_eq_cmean_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (μ : FinitePrior α) (F : ι → α → ℂ) :
    (∑i,μ.cmean (F i))=μ.cmean (fun a=>∑i,F i a) := by
  simp only [FinitePrior.cmean,Finset.mul_sum]
  exact Finset.sum_comm

theorem commonRootChoicesSum_eq_sourceMean
    (F : AllowedFrequency (frequencyBound Bs BD Bz k L) l →
      Choices (l:=l) C → Choices (l:=l) C → ℂ) :
    (∑v,choicesPairSum C (F v)) =
      (pairedInternalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).cmean
        (fun z=>∑v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
          ∑f : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
          ∑g : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
          F v
            (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
              (frequencyBound Bs BD Bz k L) l f (fun i=>z (.inl i)))
            (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
              (frequencyBound Bs BD Bz k L) l g (fun i=>z (.inr i)))) := by
  simp_rw [choicesPairSum_eq_frequency_sourceMean,sum_cmean_eq_cmean_sum]

end Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex

end

end OAI
