import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatchedOriginalSamples
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationMatchedSelectedFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalBulk
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalMatchedData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalOuter

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceCoordinates HistoryPairReferenceSourceTransport HistoryPairKernelProductReplacement
attribute [local instance] Classical.propDecidable
local instance matchedPrincipalFamilyInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

structure MatchedPrincipalBlockFamily (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ) (l : ℕ) (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) where
  active : OriginalOuter (fun _ : Bool=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p → Prop
  reference : (i : OriginalOuter (fun _ : Bool=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p) → active i →
    MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l p
  leftRootFrequency : ℤ
  rightRootFrequency : ℤ
  leftRootFrequency_eq : ∀i hi,(reference i hi).leftRoot.frequency=leftRootFrequency
  rightRootFrequency_eq : ∀i hi,(reference i hi).rightRoot.frequency=rightRootFrequency
  leftFrequency_eq : ∀i hi,(reference i hi).leftFrequency=f
  rightFrequency_eq : ∀i hi,(reference i hi).rightFrequency=g
  permutation : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length)
  rootAligned : ∀i hi t,
    coordinateSample _ (reference i hi).right.history (reference i hi).right.labels (.inr (.inl t))=
    coordinateSample _ (reference i hi).left.history (reference i hi).left.labels (.inr (.inl (permutation t)))
  principal : ∀i hi,MatchedPrincipalReferenceData C (reference i hi)

namespace MatchedPrincipalBlockFamily
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ} {l : ℕ}
  {f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  (F : MatchedPrincipalBlockFamily C outside l f g p)

def weight (corrected mixed : Bool)
    (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) : ℝ :=
  if hy : F.active (originalDrawOuter (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p y) then
    rightRootSupportIndicator (F.reference _ hy) (fun _ : Bool=>C.giant) y *
      ‖(F.principal _ hy).value corrected mixed (originalDrawBulk C l p y)‖ else 0

def toActive (corrected mixed : Bool) :
    MatchedActiveBlockFamily (fun _ : Bool=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l f g p where
  Outer := OriginalOuter (fun _ : Bool=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p
  outer := originalDrawOuter (fun _ : Bool=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p
  active := F.active
  reference := F.reference
  leftRootFrequency := F.leftRootFrequency
  rightRootFrequency := F.rightRootFrequency
  leftRootFrequency_eq := F.leftRootFrequency_eq
  rightRootFrequency_eq := F.rightRootFrequency_eq
  leftFrequency_eq := F.leftFrequency_eq
  rightFrequency_eq := F.rightFrequency_eq
  permutation := F.permutation
  rootAligned := F.rootAligned
  weight := F.weight corrected mixed

def mean (corrected mixed : Bool) : ℝ := (F.toActive corrected mixed).mean

theorem weight_nonneg (corrected mixed : Bool) (y) : 0 ≤ F.weight corrected mixed y := by
  unfold weight
  split
  · exact mul_nonneg (rightRootSupportIndicator_bounds _ _ _).1 (norm_nonneg _)
  · exact le_refl _

theorem weight_eq_guarded_principal_norm (corrected mixed : Bool) (y)
    (hy : F.active (originalDrawOuter (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p y)) :
    F.weight corrected mixed y=
      rightRootSupportIndicator (F.reference _ hy) (fun _ : Bool=>C.giant) y *
        ‖(F.principal _ hy).value corrected mixed (originalDrawBulk C l p y)‖ := by
  unfold weight
  rw [dite_eq_left hy]

theorem weight_le_principal_norm (corrected mixed : Bool) (y)
    (hy : F.active (originalDrawOuter (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p y)) :
    F.weight corrected mixed y ≤
      ‖(F.principal _ hy).value corrected mixed (originalDrawBulk C l p y)‖ := by
  rw [F.weight_eq_guarded_principal_norm corrected mixed y hy]
  exact mul_le_of_le_one_left (norm_nonneg _) (rightRootSupportIndicator_bounds _ _ _).2

theorem weight_ne_zero_rightRootSupported (corrected mixed : Bool) (y)
    (hy : F.active (originalDrawOuter (fun _ : Bool=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p y))
    (hne : F.weight corrected mixed y ≠ 0) :
    RightRootSupported (F.reference _ hy) (fun _ : Bool=>C.giant) y := by
  apply (rightRootSupportIndicator_ne_zero_iff _ _ _).mp
  intro hz
  apply hne
  rw [F.weight_eq_guarded_principal_norm corrected mixed y hy,hz,zero_mul]

end MatchedPrincipalBlockFamily
end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
