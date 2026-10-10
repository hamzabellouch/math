import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.HistoryBits
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelMember

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelLookup
open WordOperations WordList RationalLeaves
noncomputable def item (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix x))
noncomputable def item_computes : PolyComputes item :=
  (discardPrefix_computes.pair extractPrefix_computes).comp Lookup.run_computes
lemma item_pack {α : Type*} (E : α → List Bool) (xs : List α) (i : Fin xs.length) :
    item (pairBits (encode (xs.map E),i.val.bits))=E (xs.get i) := by
  simp only [item,extractPrefix_pairBits,discardPrefix_pairBits,lookup_list]
noncomputable def run : List Bool → List Bool := mapWith item
noncomputable def run_computes : PolyComputes run := mapWith_computes item_computes
lemma run_pack {α : Type*} (E : α → List Bool) (xs : List α) (is : List (Fin xs.length)) :
    run (pairBits (encode (xs.map E),BinaryOpeningActivity.indices is))=
      encode ((is.map xs.get).map E) := by
  simp only [run,BinaryOpeningActivity.indices,mapWith_encode,List.map_map,Function.comp_def,item_pack]

noncomputable def history : List Bool → List Bool := mapWith run
noncomputable def history_computes : PolyComputes history := mapWith_computes run_computes
lemma history_pack {α : Type*} (E : α → List Bool) (xs : List α) (hs : List (List (Fin xs.length))) :
    history (pairBits (encode (xs.map E),BinaryHistoryRun.historyBits hs))=
      encode ((hs.map (List.map xs.get)).map (fun H=>encode (H.map E))) := by
  simp only [history,BinaryHistoryRun.historyBits,mapWith_encode,List.map_map,Function.comp_def,run_pack]
end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

end OAI
