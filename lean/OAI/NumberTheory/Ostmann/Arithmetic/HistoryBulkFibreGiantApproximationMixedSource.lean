import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceZero

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryPairBulkTransport HistorySymbolicEncoding
open HistoryBulkReferencePeriodicMeanSource HistoryBulkReferenceSmallMultiplier
open HistorySignedResidueFactorization DiagonalSmallResidueNorm
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}

theorem Frame.sourceMeanMixed_eq (r : Frame (l:=l) C outside)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Frame.Source (C:=C) (l:=l))
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) r.s)
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length))
    (hnew : ∀i,(y i).val=(x (π i)).val)
    : r.sourceMeanMixed σ x y = staticPairMask (r.newLeft x) (r.newRight y) outside *
      oldCompensation r.left r.right*r.periodicMixed σ x y hu := by
  exact orderedReference_mixedMean_jointScalar C outside l depth σ r.leftSource r.rightSource
    x y r.s r.t r.P.toNat r.Q.toNat r.leftChoices r.rightChoices r.left_supported
    r.right_supported (bulkSize depth L/2) hu π hnew r.outside_primes

theorem Frame.sourceMeanMixed_eq_zero (r : Frame (l:=l) C outside)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Frame.Source (C:=C) (l:=l))
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length))
    (hnew : ∀i,(y i).val=(x (π i)).val)
    (hz : staticPairMask (r.newLeft x) (r.newRight y) outside=0) :
    r.sourceMeanMixed σ x y=0 := by
  exact (orderedReference_means_eq_zero_of_static C (frequencyBound Bs BD Bz depth L)
    outside l depth σ r.leftSource r.rightSource x y r.s r.t r.P.toNat r.Q.toNat
    r.leftChoices r.rightChoices r.left_supported r.right_supported
    (bulkSize depth L/2) (bulkSize depth L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
    π hnew r.outside_primes _ hz).2

theorem Frame.sourceMeanCorrectedMixed_eq (r : Frame (l:=l) C outside)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Frame.Source (C:=C) (l:=l))
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) r.s)
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length))
    (hold : ∀i,(r.rightSource i).val=(r.leftSource (π i)).val)
    (hnew : ∀i,(y i).val=(x (π i)).val)
    (hfixed : ∀i:Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length,
      ((Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).get i).role≠.bulk →
      (x i).val=(r.leftSource i).val)
    : r.sourceMeanCorrectedMixed σ x y = staticPairMask (r.newLeft x) (r.newRight y) outside *
      oldCompensation r.left r.right*r.periodicCorrectedMixed σ x y hu := by
  exact orderedReference_corrected_mixedMean_jointScalar C outside l depth σ r.leftSource r.rightSource
    x y r.s r.t r.P.toNat r.Q.toNat r.leftChoices r.rightChoices r.left_supported
    r.right_supported (bulkSize depth L/2) hu π hold hnew hfixed r.outside_primes

theorem Frame.sourceMeanCorrectedMixed_eq_zero (r : Frame (l:=l) C outside)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (x y : Frame.Source (C:=C) (l:=l))
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l).length))
    (hnew : ∀i,(y i).val=(x (π i)).val)
    (hz : staticPairMask (r.newLeft x) (r.newRight y) outside=0) :
    r.sourceMeanCorrectedMixed σ x y=0 := by
  exact (orderedReference_means_eq_zero_of_static C (frequencyBound Bs BD Bz depth L)
    outside l depth σ r.leftSource r.rightSource x y r.s r.t r.P.toNat r.Q.toNat
    r.leftChoices r.rightChoices r.left_supported r.right_supported
    (bulkSize depth L/2) (bulkSize depth L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
    π hnew r.outside_primes _ hz).2

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
