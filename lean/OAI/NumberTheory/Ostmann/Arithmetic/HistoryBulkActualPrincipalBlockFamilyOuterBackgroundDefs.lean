import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterMass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
attribute [local instance] Classical.propDecidable
local instance outerBackgroundDefsInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)

abbrev Background := (Bool→C.giant.Sample)×SelectedNonbulkSample C l

def backgroundPrior : FinitePrior (Background C l) :=
  FinitePrior.pair (dependentProductPrior (fun _ : Bool=>C.giant.law))
    (selectedNonbulkPrior C l)

variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))

def restoreOuterBackground (bg : Background C l)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p
  | ⟨.inl q,_⟩ => bg.1 q
  | ⟨.inr (.inl i),hi⟩ => bg.2 ⟨i,hi⟩
  | ⟨.inr (.inr q),_⟩ => b q

@[simp] theorem outerGiants_restoreOuterBackground (bg : Background C l)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    outerGiants C l p (restoreOuterBackground C l p bg b)=bg.1 := rfl

@[simp] theorem outerNonbulk_restoreOuterBackground (bg : Background C l)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    outerNonbulk C l p (restoreOuterBackground C l p bg b)=bg.2 := rfl

@[simp] theorem outerBlocks_restoreOuterBackground (bg : Background C l)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    outerBlocks C l p (restoreOuterBackground C l p bg b)=b := rfl

@[simp] theorem restoreOuterBackground_projections
    (o : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) :
    restoreOuterBackground C l p (outerGiants C l p o,outerNonbulk C l p o)
      (outerBlocks C l p o)=o := by
  funext i
  rcases i with ⟨i,hi⟩
  rcases i with q | i | q <;> rfl

def outerBackgroundEquiv :
    OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p ≃
      Background C l × (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) where
  toFun o := ((outerGiants C l p o,outerNonbulk C l p o),outerBlocks C l p o)
  invFun z := restoreOuterBackground C l p z.1 z.2
  left_inv := restoreOuterBackground_projections C l p
  right_inv z := by
    rcases z with ⟨⟨g,a⟩,b⟩
    rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
