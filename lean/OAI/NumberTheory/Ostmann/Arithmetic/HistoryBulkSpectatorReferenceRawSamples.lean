import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawLeaves

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction Characters HistoryBulkProducts CanonicalHistoryLeafBulk

def sourceBulkUnits (M : ℕ) (sources : SourceFamily) (m k l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (u : Fin (2^l)×Fin m) : (ZMod M)ˣ :=
  Characters.Template.unitConvention (bulkSamples sources m k l x u.1 u.2:ZMod M)

theorem bulkProduct_assigned_eq_prod (sources : SourceFamily) (m k l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l)) :
    bulkProduct (assignedSlots sources (Template.current (Template.initial m k) l) x)=
      ∏b:Fin (2^l),∏i:Fin m,bulkSamples sources m k l x b i := by
  change (bulkValues _).prod=_
  rw [bulkValues_assignedSlots]
  simp [rows,List.prod_flatten,List.map_ofFn,List.prod_ofFn,Function.comp_def]

theorem bulkSamples_dvd_bulkProduct (sources : SourceFamily) (m k l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (u : Fin (2^l)×Fin m) :
    bulkSamples sources m k l x u.1 u.2 ∣
      bulkProduct (assignedSlots sources (Template.current (Template.initial m k) l) x) := by
  rw [bulkProduct_assigned_eq_prod]
  exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ u.2)).trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ u.1))

theorem sourceBulkUnits_coe (M : ℕ) (sources : SourceFamily) (m k l : ℕ)
    (x : SourceAssignment sources (Template.current (Template.initial m k) l))
    (hc : Nat.Coprime (bulkProduct
      (assignedSlots sources (Template.current (Template.initial m k) l) x)) M)
    (u : Fin (2^l)×Fin m) :
    (sourceBulkUnits M sources m k l x u:ZMod M)=(bulkSamples sources m k l x u.1 u.2:ZMod M) :=
  Characters.Template.unitConvention_coe _ ((ZMod.isUnit_iff_coprime _ _).mpr
    (hc.of_dvd_left (bulkSamples_dvd_bulkProduct sources m k l x u)))

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
