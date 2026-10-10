import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupportBasic
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesMass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryPairSourceLaws HistoryCompensationRepresentativePatterns
attribute [local instance] Classical.propDecidable
local instance actualPrincipalOuterSupportInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)

theorem outerMass_sourceWeight_ne_zero (ho : outerMass C l p o ≠ 0)
    (i : Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
      Internal (Template.initial (2*(bulkSize k L/2)) k) l) :
    sourceWeight C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      i (outerBlocks C l p o (label p i)) ≠ 0 :=
  biasedBlockWeight_source_nonzero C.sources _ p (label p i) _
    (outerMass_ne_zero_block C l p o ho (label p i)) ⟨i,rfl⟩

theorem outerMass_valid (ho : outerMass C l p o ≠ 0) :
    ∀ i, (outerBlocks C l p o (label p i)).val ∈
      (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).candidates := by
  intro i
  have hi := outerMass_sourceWeight_ne_zero C p o ho i
  unfold sourceWeight at hi
  split_ifs at hi with hm
  · exact hm
  · exact (hi rfl).elim

theorem outerData_nonempty_of_mass (ho : outerMass C l p o ≠ 0)
    (ht : Function.Injective (fun q=> (blockType p q,outerBlocks C l p o q))) :
    Nonempty (OuterData C p o) := by
  let hv := outerMass_valid C p o ho
  have ha : 0 < (selectedNonbulkPrior C l).mass (outerNonbulk C l p o) :=
    lt_of_le_of_ne ((selectedNonbulkPrior C l).mass_nonneg _) (Ne.symm (outerMass_ne_zero_nonbulk C l p o ho))
  have hm : ∀ i, (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).law.mass
      ⟨(outerBlocks C l p o (label p i)).val,hv i⟩ ≠ 0 := by
    intro i
    have hi := outerMass_sourceWeight_ne_zero C p o ho i
    simpa only [sourceWeight,dite_eq_left (hv i)] using hi
  refine ⟨⟨ht,hv,ha,?_,?_⟩⟩
  · intro i
    rw [leftChoices,choicesMass_assemble]
    change (∏ j : Internal (Template.initial (2*(bulkSize k L/2)) k) l,
      (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l (Sum.inl j))).law.mass
        ⟨(outerBlocks C l p o (label p (Sum.inl j))).val,hv (Sum.inl j)⟩) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun j _=>hm (Sum.inl j))
  · intro i
    rw [rightChoices,choicesMass_assemble]
    change (∏ j : Internal (Template.initial (2*(bulkSize k L/2)) k) l,
      (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l (Sum.inr j))).law.mass
        ⟨(outerBlocks C l p o (label p (Sum.inr j))).val,hv (Sum.inr j)⟩) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun j _=>hm (Sum.inr j))

theorem outerData?_isSome_of_mass (ho : outerMass C l p o ≠ 0)
    (ht : Function.Injective (fun q=> (blockType p q,outerBlocks C l p o q))) :
    (outerData? C p o).isSome :=
  (outerData?_isSome_iff C p o).mpr (outerData_nonempty_of_mass C p o ho ht)

theorem outerMass_eq_zero_of_outerData_none
    (ht : Function.Injective (fun q=> (blockType p q,outerBlocks C l p o q)))
    (hn : outerData? C p o = none) : outerMass C l p o = 0 := by
  by_contra ho
  have hp := outerData?_isSome_of_mass C p o ho ht
  rw [hn] at hp
  contradiction

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
