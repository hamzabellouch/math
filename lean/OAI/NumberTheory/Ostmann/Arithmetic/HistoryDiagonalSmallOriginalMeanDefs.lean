import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorizationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationCRTSelectedBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean
open Construction Conclusion HistorySignedResidues HistorySignedXiTransport HistorySymbolicEncoding
open HistoryGiantReferenceMean HistoryGiantPriorGrid HistoryCRTIntegration
open HistoryDiagonalSmallAverage HistorySignedResidueFactorization
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

abbrev outerAssignment (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l))) :=
  (restoringAssignmentEquiv C.sources (l+1) _ x).1

abbrev smallAssignment (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l))) :=
  (restoringAssignmentEquiv C.sources (l+1) _ x).2

def smallMultiplier (outside : List ℕ)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s P Q : ℤ) : ℝ :=
  diagonalSmallMultiplier d
    (outside.prod * halfProduct P.toNat (assignedSlots C.sources _ (outerAssignment C x)))
    s Q.toNat (assignedSlots C.sources _ (smallAssignment C x))

def originalMixedMean (outside : List ℕ)
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C) : ℂ :=
  mixedMean C.giantCenter C.giant
    (sourceIntegrand d C.sources _ (frequencyBound Bs BD Bz k L) outside l
      (sourceState C.sources _ x s) (sourceState C.sources _ y t) c e
      (fun P Q => (smallMultiplier C outside x s P Q:ℂ))
      (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter)

variable (outside : List ℕ)
variable (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
variable (s t P Q : ℤ) (c e : Choices (l:=l) C)
variable (hs : (history C x s P Q c).Supported (frequencyBound Bs BD Bz k L) outside)
variable (hsource : ∀ i : Fin (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))).length,
  (C.sources ((Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))).get i).origin).AboveFrequency
    (frequencyBound Bs BD Bz k L l))
variable (hx : (assignmentPrior C.sources _).mass (smallAssignment C x) ≠ 0)

theorem history_root_split_perm :
    (history C x s P Q c).root.small.Perm
      (assignedSlots C.sources _ (outerAssignment C x) ++
       assignedSlots C.sources _ (smallAssignment C x)) := by
  rw [history_small_split C x s P Q c]
  exact Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _)

def sourceWeight (n : ℕ) :
    ZMod (comparisonModulus (history C x s P Q c) (history C y t P Q e) outside n) ×
      ZMod (comparisonModulus (history C x s P Q c) (history C y t P Q e) outside n) → ℂ :=
  fun z => (sourceLiftedRootSmallTest d C.sources _ _ (smallAssignment C x)
    (outerAssignment C x) (history C x s P Q c) hs
    (history_root_split_perm C x s P Q c) hsource hx
    (comparisonModulus (history C x s P Q c) (history C y t P Q e) outside n)
    (rootModulus_dvd_comparisonModulus _ _ _ n) z:ℂ)

theorem sourceWeight_norm_le (gs : (history C y t P Q e).Supported (frequencyBound Bs BD Bz k L) outside)
    (hout : ∀ q ∈ outside, q.Prime) (n : ℕ) (z) :
    ‖sourceWeight C outside x y s t P Q c e hs hsource hx n z‖ ≤
      (comparisonModulus (history C x s P Q c) (history C y t P Q e) outside n:ℝ) := by
  exact sourceLiftedRootSmallTest_norm_le_modulus d C.sources _ _ (smallAssignment C x)
    (outerAssignment C x) (history C x s P Q c) hs
    (history_root_split_perm C x s P Q c) hsource hx _
    (rootModulus_dvd_comparisonModulus _ _ _ n)
    (comparisonModulus_pos _ _ hs gs hout n) z

end Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean

end

end OAI
