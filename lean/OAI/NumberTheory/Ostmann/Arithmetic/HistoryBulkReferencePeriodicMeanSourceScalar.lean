import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceMaskPeriodic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource
open Construction Conclusion HistoryPairPattern HistoryPairSmoothXi HistoryBulkReferenceScalarCoordinates
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistoryBulkGiantCorrectedBounds HistoryBulkIntegralReplacement
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

def staticPairMask (h k : History l) (outside : List ℕ) : ℂ :=
  HistorySignedResidueFactorization.guardIndicator
    ((h.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
      (k.root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime)

def oldCompensation (h k : History l) : ℂ :=
  (h.compensationProduct:ℂ)*(k.compensationProduct:ℂ)

def primeScalar (b sw : ℕ) (X tb td G : ℝ) (m depth : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m depth) l) h.root.small)
    (x : Fin (2^l)×Fin m→ℝ) (u : Bool→ℝ) : ℂ :=
  pairedRealXi b sw X tb td G h k hs ks (insertOrderedGiants m depth h k hs hh x u)

def mixedScalar (b sw : ℕ) (X tb td G : ℝ) (m depth : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m depth) l) h.root.small)
    (x : Fin (2^l)×Fin m→ℝ) (u : Option Unit→ℝ) : ℂ :=
  primeScalar b sw X tb td G m depth h k hs ks hh x
    (fun t=>if t then u (some ()) else u none)

theorem primeScalar_eq_jointScalar {d : Decomposition} {Bs BD Bz L : ℝ} {depth : ℕ}
    {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz depth L E)
    (sw : ℕ) (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz depth L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz depth L) outside)
    (hh : Template.Matches (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l) h.root.small)
    (x : Fin (2^l)×Fin (2*(bulkSize depth L/2))→ℝ) (u : Bool→ℝ) :
    primeScalar (bulkSize depth L/2) sw C.scale C.bulkBin C.spectatorBin C.giantCenter
      (2*(bulkSize depth L/2)) depth h k hs ks hh x u =
    jointScalar C sw h k hs ks (boolEquiv h k)
      (orderedEquiv (2*(bulkSize depth L/2)) depth h k hs hh) u x := by
  unfold primeScalar jointScalar reindexedRealXi activeRealXi
  rw [insertOrderedGiants_eq_bulk_over_giants]
  rfl

end Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource

end

end OAI
