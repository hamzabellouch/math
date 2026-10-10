import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSelectedFamily

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceSourceTransport
attribute [local instance] Classical.propDecidable
local instance principalOuterInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {sources : SourceFamily} {seed : List SourceSlot} {l : ℕ}

def originalIndexIsBulk (p : Pattern (pairedHistoryType seed l)) : TypedSourceIndex p → Prop
  | .inl _ => False
  | .inr (.inl i) => ((Template.current seed l).get i).role=.bulk
  | .inr (.inr _) => False

abbrev OriginalOuter (giants : Bool→PrimeSource) (sources : SourceFamily)
    (seed : List SourceSlot) (l : ℕ) (p : Pattern (pairedHistoryType seed l)) :=
  ∀i : {i : TypedSourceIndex p // ¬originalIndexIsBulk p i},
    mixedCarrier giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i.val

def originalDrawOuter (giants : Bool→PrimeSource) (sources : SourceFamily)
    (seed : List SourceSlot) (l : ℕ) (p : Pattern (pairedHistoryType seed l))
    (y : OriginalDraw giants sources seed l p) : OriginalOuter giants sources seed l p :=
  fun i=>y i.val

theorem originalDrawOuter_eq (giants : Bool→PrimeSource) (p : Pattern (pairedHistoryType seed l))
    (y z : OriginalDraw giants sources seed l p)
    (h : ∀i,¬originalIndexIsBulk p i → y i=z i) :
    originalDrawOuter giants sources seed l p y=originalDrawOuter giants sources seed l p z := by
  funext i
  exact h i.val i.property

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
