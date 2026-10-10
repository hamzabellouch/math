import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuter

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance actualPrincipalOuterMassInternalDecidable (template : List SourceSlot) (l : ℕ) : DecidableEq (Internal template l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)
variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))

def outerMass (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) : ℝ :=
  (∏q:Bool,C.giant.law.mass (outerGiants C l p o q)) *
    (selectedNonbulkPrior C l).mass (outerNonbulk C l p o) *
    ∏q:Block p,biasedBlockWeight C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p q (outerBlocks C l p o q)

theorem outerMass_nonneg (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    0 ≤ outerMass C l p o := by
  unfold outerMass
  apply mul_nonneg
  · exact mul_nonneg (Finset.prod_nonneg (fun q _=>C.giant.law.mass_nonneg _))
      ((selectedNonbulkPrior C l).mass_nonneg _)
  · exact Finset.prod_nonneg (fun q _=>HistoryPairSourceFlagReplacement.biasedBlockWeight_nonneg _ _ _ _ _)

theorem originalDrawMass_eq_outerMass_mul_bulkMass
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    originalDrawMass (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y =
      outerMass C l p (originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y) *
      (selectedBulkPrior C l).mass (originalDrawBulk C l p y) := by
  rw [originalDrawMass,mixed_weight_product]
  have hm := congrArg (fun x=>(assignmentPrior C.sources (SelectedTemplate k L l)).mass x)
    (originalDrawAssignment_eq_fibreAssignment C l p y)
  rw [fibreAssignment_mass] at hm
  change (∏q:Bool,C.giant.law.mass (y (.inl q))) *
    ((assignmentPrior C.sources (SelectedTemplate k L l)).mass (originalDrawAssignment C l p y) *
      ∏q:Block p,biasedBlockWeight C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) p q (y (.inr (.inr q)))) = _
  rw [hm]
  simp only [outerMass,outerGiants_originalDrawOuter,outerBlocks_originalDrawOuter]
  ring

theorem originalDrawMass_ne_zero_iff
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    originalDrawMass (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y≠0 ↔
      outerMass C l p (originalDrawOuter (fun _=>C.giant) C.sources
        (Template.initial (2*(bulkSize k L/2)) k) l p y)≠0 ∧
      (selectedBulkPrior C l).mass (originalDrawBulk C l p y)≠0 := by
  rw [originalDrawMass_eq_outerMass_mul_bulkMass,mul_ne_zero_iff]

theorem outerMass_ne_zero_nonbulk
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (ho : outerMass C l p o≠0) :
    (selectedNonbulkPrior C l).mass (outerNonbulk C l p o)≠0 :=
  (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).2

theorem outerMass_ne_zero_block
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (ho : outerMass C l p o≠0) (q : Block p) :
    biasedBlockWeight C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      p q (outerBlocks C l p o q)≠0 :=
  (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).2) q (Finset.mem_univ q)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
