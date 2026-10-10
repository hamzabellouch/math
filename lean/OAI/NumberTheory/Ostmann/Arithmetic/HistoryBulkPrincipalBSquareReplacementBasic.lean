import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum
open HistoryPairVariableBSquareErrorSelected HistoryBulkPrincipalCollisionError
attribute [local instance] Classical.propDecidable
local instance squareBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

structure PrincipalSquareReference (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) where
  square : DecodedSquareReference C
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) p b
    (frequencyBound Bs BD Bz k L) outside l
  principal : PrincipalAmplitudeData C outside l
  left_eq : principal.left = square.leftDraw.history
  right_eq : principal.right = square.rightDraw.history
  newBulk : (Fin (2^l) × Fin (2*(bulkSize k L/2))) → C.bulk.Sample

variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

abbrev ReferenceFamily (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ) (l : ℕ) :=
  ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
      Option (PrincipalSquareReference C outside l p b)

def squareReferences (R : ReferenceFamily C outside l) :=
  fun p b => (R p b).map PrincipalSquareReference.square

def principalAmplitude (R : ReferenceFamily C outside l) (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : BlockDraw p (CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))) : ℂ :=
  match R p b.val with
  | none => 0
  | some r => r.principal.value corrected mixed r.newBulk

def principalBErrorSum (R : ReferenceFamily C outside l) (corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop) : ℂ :=
  weightedOriginalDecodedBErrorSum C
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
    mixed (frequencyBound Bs BD Bz k L) outside l (squareReferences R)
    (fun p b => if mask p b then 1 else 0) (principalAmplitude R corrected mixed)

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement

end

end OAI
