import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanDefs
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexBands

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean
open Construction Conclusion
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean
open HistoryDiagonalSmallOriginalMean hiding originalMixedMean

def smallCounterpartCoordinate (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) (e : Equiv.Perm (RemainingIndex T))
    (i : Fin T.length) : ℕ :=
  Fin.cases 0 (fun j => (x j).val) (e i.succ)

def SmallCounterpartCompatible (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) (e : Equiv.Perm (RemainingIndex T)) : Prop :=
  ∀ i, smallCounterpartCoordinate sources T x e i ∈ (sources T[i].origin).candidates

def reconstructSmallCounterpart (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) (e : Equiv.Perm (RemainingIndex T))
    (hc : SmallCounterpartCompatible sources T x e) : SourceAssignment sources T :=
  fun i => ⟨smallCounterpartCoordinate sources T x e i, hc i⟩

theorem smallCounterpartCoordinate_eq (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (q : giant.Sample) (x : SourceAssignment sources T)
    (e : Equiv.Perm (RemainingIndex T)) (hb : PreservesRemainingBands T e) (i : Fin T.length) :
    smallCounterpartCoordinate sources T x e i = remainingCoordinate sources T giant (q,x) (e i.succ) := by
  have hz : e i.succ ≠ 0 := by
    intro hi
    exact Fin.succ_ne_zero i (e.injective (hi.trans hb.fixes_giant.symm))
  unfold smallCounterpartCoordinate remainingCoordinate
  generalize he : e i.succ = z at hz ⊢
  induction z using Fin.cases with
  | zero => exact (hz rfl).elim
  | succ z => rfl

theorem counterpartCompatible_iff_small (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (q : giant.Sample) (x : SourceAssignment sources T)
    (e : Equiv.Perm (RemainingIndex T)) (hb : PreservesRemainingBands T e) :
    CounterpartCompatible sources T giant (q,x) e ↔ SmallCounterpartCompatible sources T x e := by
  constructor
  · intro hc i
    rw [smallCounterpartCoordinate_eq sources T giant q x e hb i]
    exact hc i.succ
  · intro hc i
    induction i using Fin.cases with
    | zero => simpa only [hb.fixes_giant, remainingCoordinate, remainingPositionSource,
        Fin.cases_zero] using q.property
    | succ i =>
      have hi := hc i
      rw [smallCounterpartCoordinate_eq sources T giant q x e hb i] at hi
      exact hi

theorem reconstructCounterpart_eq_small (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (q : giant.Sample) (x : SourceAssignment sources T)
    (e : Equiv.Perm (RemainingIndex T)) (hb : PreservesRemainingBands T e)
    (hc : CounterpartCompatible sources T giant (q,x) e) :
    reconstructCounterpart sources T giant (q,x) e hc =
      (q, reconstructSmallCounterpart sources T x e
        ((counterpartCompatible_iff_small sources T giant q x e hb).mp hc)) := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [reconstructCounterpart, hb.fixes_giant, remainingCoordinate, Fin.cases_zero]
  · funext i
    apply Subtype.ext
    exact (smallCounterpartCoordinate_eq sources T giant q x e hb i).symm

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def counterpartCurrentAssignment (C : InitialSourceChoice d Bs BD Bz k L E)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))))
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C x) e) :
    SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)) :=
  (restoringAssignmentEquiv C.sources (l+1) _).symm
    (outerAssignment C x, reconstructSmallCounterpart C.sources _ (smallAssignment C x) e hc)

@[simp] theorem counterpartCurrentAssignment_outer (C : InitialSourceChoice d Bs BD Bz k L E)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))))
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C x) e) :
    outerAssignment C (counterpartCurrentAssignment C x e hc) = outerAssignment C x := by
  simp only [outerAssignment, counterpartCurrentAssignment, Equiv.apply_symm_apply]

@[simp] theorem counterpartCurrentAssignment_small (C : InitialSourceChoice d Bs BD Bz k L E)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))))
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C x) e) :
    smallAssignment C (counterpartCurrentAssignment C x e hc) =
      reconstructSmallCounterpart C.sources _ (smallAssignment C x) e hc := by
  exact congrArg Prod.snd ((restoringAssignmentEquiv C.sources (l+1)
    (Current (k:=k) (L:=L) (l:=l))).apply_symm_apply
      (outerAssignment C x, reconstructSmallCounterpart C.sources _ (smallAssignment C x) e hc))

end Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean

end

end OAI
