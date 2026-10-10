import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanEnergyBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesPermutation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
open Construction HistoryDiagonalCorrectedOriginalMean

def smallPermutation {T : List SourceSlot} (e : Equiv.Perm (RemainingIndex T))
    (he : PreservesRemainingBands T e) : Equiv.Perm (Fin T.length) where
  toFun i := (e i.succ).pred (by
    intro h
    exact Fin.succ_ne_zero i (e.injective (h.trans he.fixes_giant.symm)))
  invFun i := (e.symm i.succ).pred (by
    intro h
    have hh := congrArg e h
    simp only [Equiv.apply_symm_apply,he.fixes_giant] at hh
    exact Fin.succ_ne_zero i hh)
  left_inv i := by simp
  right_inv i := by simp

@[simp] theorem smallPermutation_succ {T : List SourceSlot}
    (e : Equiv.Perm (RemainingIndex T)) (he : PreservesRemainingBands T e)
    (i : Fin T.length) : (smallPermutation e he i).succ = e i.succ := by
  simp only [smallPermutation, Equiv.coe_fn_mk, Fin.succ_pred]

theorem smallPermutation_role {T : List SourceSlot}
    (e : Equiv.Perm (RemainingIndex T)) (he : PreservesRemainingBands T e)
    (i : Fin T.length) : (T.get (smallPermutation e he i)).role = (T.get i).role := by
  exact he.role_eq i (smallPermutation e he i) (smallPermutation_succ e he i).symm

@[simp] theorem reconstructSmallCounterpart_val (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) (e : Equiv.Perm (RemainingIndex T))
    (he : PreservesRemainingBands T e)
    (hc : SmallCounterpartCompatible sources T x e) (i : Fin T.length) :
    (reconstructSmallCounterpart sources T x e hc i).val = (x (smallPermutation e he i)).val := by
  change smallCounterpartCoordinate sources T x e i = _
  unfold smallCounterpartCoordinate
  rw [←smallPermutation_succ e he i]
  rfl

theorem right_nonbulk_fixed {sources : SourceFamily} {T : List SourceSlot}
    (π : Equiv.Perm (Fin T.length))
    (hrole : ∀i, (T.get (π i)).role = (T.get i).role)
    (x₀ y₀ x y : SourceAssignment sources T)
    (hold : ∀i, (y₀ i).val = (x₀ (π i)).val)
    (hnew : ∀i, (y i).val = (x (π i)).val)
    (hfixed : ∀i, (T.get i).role ≠ .bulk → (x i).val = (x₀ i).val) :
    ∀i, (T.get i).role ≠ .bulk → (y i).val = (y₀ i).val := by
  intro i hi
  rw [hnew i, hold i]
  exact hfixed (π i) (by simpa only [hrole i] using hi)

end Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching

end

end OAI
