import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BlueItem

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueBlocks
open WordOperations WordList
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
def labelsEnc (el : L→List Bool) (U : Finset L) : List Bool := WordList.encode ((U.sort (·≤·)).map el)
noncomputable def itemCall (x : List Bool) : List Bool := BinaryBlueItem.run
  (pairBits (pairBits (discardPrefix x,discardPrefix (extractPrefix x)),extractPrefix (extractPrefix x)))
noncomputable def itemCall_computes : PolyComputes itemCall :=
  ((discardPrefix_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).pair
    (extractPrefix_computes.comp extractPrefix_computes)).comp BinaryBlueItem.run_computes
noncomputable def atCenter (x : List Bool) : List Bool := BinaryBlueCollect.run (mapWith itemCall x)
noncomputable def at_computes : PolyComputes atCenter := (mapWith_computes itemCall_computes).comp BinaryBlueCollect.run_computes
lemma at_pack (el : L→List Bool) (er : R→List Bool) (hel : Function.Injective el) (B : Finset R)
    (label : R→L) (q : R→Fin n→ℚ) (U : Finset L) (y : Fin n) :
    atCenter (pairBits (pairBits (BinaryBlueItem.records el er B label q,y.val.bits),labelsEnc el U))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc el er)) (BlueDP.blockAt B label q U y) := by
  simp only [atCenter,labelsEnc,mapWith_encode,List.map_map,Function.comp_def,itemCall,extractPrefix_pairBits,
    discardPrefix_pairBits,BinaryBlueItem.run_pack el er hel]
  simpa only [List.map_map,Function.comp_def,BlueDP.blockAt] using
    BinaryBlueCollect.run_pack (BinaryBlueItem.atomEnc el er) ((U.sort (·≤·)).map (fun l=>BlueDP.item B label q l y))
noncomputable def atCall (x : List Bool) : List Bool := atCenter
  (pairBits (pairBits (extractPrefix (extractPrefix x),discardPrefix x),discardPrefix (extractPrefix x)))
noncomputable def atCall_computes : PolyComputes atCall :=
  (((extractPrefix_computes.comp extractPrefix_computes).pair discardPrefix_computes).pair
    (extractPrefix_computes.comp discardPrefix_computes)).comp at_computes
noncomputable def run (x : List Bool) : List Bool := BinaryBlueChoice.select (mapWith atCall x)
noncomputable def run_computes : PolyComputes run := (mapWith_computes atCall_computes).comp BinaryBlueChoice.select_computes
lemma run_pack (el : L→List Bool) (er : R→List Bool) (hel : Function.Injective el) (B : Finset R) (F : Finset (Fin n))
    (label : R→L) (q : R→Fin n→ℚ) (U : Finset L) :
    run (pairBits (pairBits (BinaryBlueItem.records el er B label q,labelsEnc el U),BinaryFinSet.encode F))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc el er)) (BlueDP.block B F label q U) := by
  simp only [run,BinaryFinSet.encode_eq,mapWith_encode,List.map_map,Function.comp_def,atCall,extractPrefix_pairBits,
    discardPrefix_pairBits,at_pack el er hel]
  rw [BinaryBlueChoice.select_map]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryBlueBlocks

end OAI
