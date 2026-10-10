import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCompensation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryGiantOriginalMeanFactorization HistoryPairSourceLaws
open HistoryBulkFibreGiantErrorAverage
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance principalReindexCancellationInternalDecidable (template : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal template l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)

theorem pairedChoiceCompensation_assemble
    (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)
    (z : PairedInternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l) :
    (pairedChoiceCompensation C
      (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) l f (fun i=>z (.inl i)))
      (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) l g (fun i=>z (.inr i))):ℂ) =
      occurrenceJacobian C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (tupleEmbed C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) z) := by
  simp only [pairedChoiceCompensation,choiceCompensation,
    occurrenceJacobian,Nat.cast_prod,Fintype.prod_sum_type,Complex.ofReal_mul,
    tupleEmbed,sourceEmbed]
  erw [historyDraws_assemble, historyDraws_assemble]

theorem choicePatternValue_compensation_cancel
    (G : Choices (l:=l) C → Choices (l:=l) C → ℂ)
    (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (hvalid : ∀i,(b (label p i)).val ∈
      (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).candidates) :
    choicePatternValue C (fun c e=>(pairedChoiceCompensation C c e:ℂ)*G c e) f g p b =
      pairedChoiceTest C G f g (fun i=>⟨(b (label p i)).val,hvalid i⟩) := by
  unfold choicePatternValue sourcePatternValue
  rw [extendSourceTest,dite_eq_left hvalid]
  change ((pairedChoiceCompensation C _ _:ℂ)*pairedChoiceTest C G f g
      (fun i=>⟨(b (label p i)).val,hvalid i⟩)) /
      occurrenceJacobian C.sources _ (fun i=>b (label p i)) = _
  rw [pairedChoiceCompensation_assemble C f g (fun i=>⟨(b (label p i)).val,hvalid i⟩)]
  have heq : tupleEmbed C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (fun i=>⟨(b (label p i)).val,hvalid i⟩) = (fun i=>b (label p i)) := by
    funext i
    apply Subtype.ext
    rfl
  rw [heq,mul_comm, mul_div_cancel_right₀ _ (occurrenceJacobian_ne_zero _ _ _)]

end Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex

end

end OAI
