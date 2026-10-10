import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormActualSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitData
open Construction DiagonalSmallResidueNorm

theorem stateSmallPrimeFacts (a : State) (hp : a.PrimeSmall)
    (outerU xs : List SmallSlot) (hslots : a.small.Perm (outerU++xs)) :
    ∀i,Fact (smallPrime xs outerU i).Prime := by
  intro i
  constructor
  cases i with
  | inl i =>
    exact hp xs[i] (hslots.mem_iff.mpr
      (List.mem_append_right _ (List.getElem_mem i.isLt)))
  | inr i =>
    exact hp outerU[i] (hslots.mem_iff.mpr
      (List.mem_append_left _ (List.getElem_mem i.isLt)))

theorem smallUnitData_of_static (a : State) (hp : a.PrimeSmall)
    (outerU xs : List SmallSlot) (outside : List ℕ)
    (hslots : a.small.Perm (outerU++xs))
    (hstatic : (a.small.map SmallSlot.value ++ outside).Pairwise Nat.Coprime)
    (hv : a.frequency ≠ 0)
    (hlarge : ∀i : Fin xs.length,a.frequency.natAbs < xs[i].value) :
    SmallUnitData outside.prod 1 1 outerU xs a.frequency := by
  have := stateSmallPrimeFacts a hp outerU xs hslots
  have hall : (outerU.map SmallSlot.value ++ xs.map SmallSlot.value ++ outside).Pairwise
      Nat.Coprime := by
    simpa only [List.map_append] using
      (((hslots.map SmallSlot.value).append_right outside).pairwise_iff Nat.Coprime.symm).mp hstatic
  apply smallUnitData_of_pairwise 1 1 outerU xs outside a.frequency _ hv hlarge
  exact List.pairwise_cons.mpr ⟨fun _ _ => Nat.coprime_one_left _,
    List.pairwise_cons.mpr ⟨fun _ _ => Nat.coprime_one_left _,hall⟩⟩

end Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitData

end

end OAI
