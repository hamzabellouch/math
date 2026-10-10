import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FinImages

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
def enum (S : Finset α) : Fin S.card→α := S.orderEmbOfFin rfl
lemma enum_mem (S : Finset α) (i : Fin S.card) : enum S i∈S := S.orderEmbOfFin_mem rfl i
lemma enum_injective (S : Finset α) : Function.Injective (enum S) := (S.orderEmbOfFin rfl).injective
lemma enum_list (S : Finset α) : List.ofFn (enum S)=S.sort (·≤·) := by
  rw [List.ofFn_eq_map]
  exact S.listMap_orderEmbOfFin_finRange rfl
lemma map_enum {β : Type*} (S : Finset α) (f : α→β) :
    (S.sort (·≤·)).map f=List.ofFn (fun i=>f (enum S i)) := by rw [←enum_list,List.map_ofFn]; rfl
end MetricKMedianRecovery.SortedIndex
namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
lemma table_enum {n : ℕ} (S : Finset (Fin n)) : table (SortedIndex.enum S)=encode S := by
  unfold table
  rw [←SortedIndex.map_enum S (fun i : Fin n=>i.val.bits),encode_eq]
end MetricKMedianRecovery.BitMachine.BinaryFinSet
namespace MetricKMedianRecovery.BitMachine.BinaryMetricArrays
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n p q : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (rows : Fin p→Fin n) (cols : Fin q→Fin n) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.table rows,BinaryFinSet.table cols]
noncomputable def row (x : List Bool) : List Bool := Lookup.run
  (pairBits (discardPrefix x,field 0 (extractPrefix x)))
noncomputable def row_computes : PolyComputes row :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 0))).comp Lookup.run_computes
lemma row_pair (δ : Fin n→Fin n→ℚ) (rows : Fin p→Fin n) (cols : Fin q→Fin n) (y : Fin n) :
    row (pairBits (pack δ rows cols,y.val.bits))=RationalMatrix.rowEncode (δ y) := by
  simp only [row,pack,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    Option.getD_some,RationalMatrix.encode,lookup_ofFn]
noncomputable def column (x : List Bool) : List Bool := BinaryIndexMap.run
  (pairBits (row x,field 2 (extractPrefix x)))
attribute [local irreducible] BinaryIndexMap.run
noncomputable def column_computes : PolyComputes column :=
  (row_computes.pair (extractPrefix_computes.comp (field_computes 2))).comp BinaryIndexMap.run_computes
lemma column_pair (δ : Fin n→Fin n→ℚ) (rows : Fin p→Fin n) (cols : Fin q→Fin n) (y : Fin n) :
    column (pairBits (pack δ rows cols,y.val.bits))=RationalMatrix.rowEncode (fun j=>δ y (cols j)) := by
  rw [column,row_pair]
  simp only [extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,
    Option.getD_some,RationalMatrix.rowEncode_eq,BinaryFinSet.table,BinaryIndexMap.run,mapWith_ofFn,
    BinaryIndexMap.item,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn]
noncomputable def run (x : List Bool) : List Bool := mapWith column (pairBits (x,field 1 x))
attribute [local irreducible] mapWith
noncomputable def run_computes : PolyComputes run :=
  (id_computes.pair (field_computes 1)).comp (mapWith_computes column_computes)
lemma run_pack (δ : Fin n→Fin n→ℚ) (rows : Fin p→Fin n) (cols : Fin q→Fin n) :
    run (pack δ rows cols)=encode (List.ofFn (fun i=>RationalMatrix.rowEncode (fun j=>δ (rows i) (cols j)))) := by
  unfold run
  rw [show field 1 (pack δ rows cols)=BinaryFinSet.table rows by simp [pack,field_encode]]
  simp only [BinaryFinSet.table,mapWith_ofFn,column_pair]
end MetricKMedianRecovery.BitMachine.BinaryMetricArrays

end OAI
