import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.SuffixMachine
import OAI.Combinatorics.KMedianRecovery.Encoding.LengthEncode

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] WordList.mapWith
noncomputable def freeOp (x : List Bool) : List Bool := encode [(0:ℕ).bits,extractPrefix x,discardPrefix x,[],[]]
noncomputable def freeOp_computes : PolyComputes freeOp :=
  list_computes [fun _=>(0:ℕ).bits,extractPrefix,discardPrefix,fun _=>[],fun _=>[]] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨extractPrefix_computes⟩
    · exact ⟨discardPrefix_computes⟩
    · exact ⟨const_computes _⟩
    · exact ⟨const_computes _⟩)
noncomputable def paidOp (x : List Bool) : List Bool := encode [(1:ℕ).bits,pf 1 x,[],pf 0 x,pf 2 x]
noncomputable def paidOp_computes : PolyComputes paidOp :=
  list_computes [fun _=>(1:ℕ).bits,pf 1,fun _=>[],pf 0,pf 2] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨pf_computes _⟩
    · exact ⟨const_computes _⟩
    · exact ⟨pf_computes _⟩
    · exact ⟨pf_computes _⟩)
noncomputable def frees (x : List Bool) : List Bool := crossWith freeOp (pairBits (field 1 x,field 3 x))
noncomputable def frees_computes : PolyComputes frees :=
  ((field_computes 1).pair (field_computes 3)).comp (crossWith_computes freeOp_computes)
noncomputable def paids (x : List Bool) : List Bool := mapWith paidOp (pairBits ([],Slices.run (field 2 x)))
noncomputable def paids_computes : PolyComputes paids :=
  ((const_computes []).pair ((field_computes 2).comp Slices.run_computes)).comp (mapWith_computes paidOp_computes)
noncomputable def candidates (x : List Bool) : List Bool := frees x++paids x
noncomputable def candidates_computes : PolyComputes candidates := frees_computes.append paids_computes
lemma frees_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : frees (ctxBits distance F R H G)=
      encode ((R.flatMap (fun i=>G.map (Plan.free i))).map planBits) := by
  simp only [frees,ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    labels,crossWith_encode,List.flatMap_map,List.map_map,Function.comp_def,List.map_flatMap,
    freeOp,extractPrefix_pairBits,discardPrefix_pairBits,planBits]
lemma paids_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : paids (ctxBits distance F R H G)=
      encode (((cuts H).map (fun p=>Plan.paid p.1 p.2.2 p.2.1)).map planBits) := by
  have hh : field 2 (ctxBits distance F R H G)=labels H := by
    simp only [ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [paids,hh,BinarySuffix.slices_labels,Slices.outBits,mapWith_encode,List.map_map,
    Function.comp_def,paidOp,pf,discardPrefix_pairBits,
    (BinarySuffix.cut_fields _).1,(BinarySuffix.cut_fields _).2.1,(BinarySuffix.cut_fields _).2.2,planBits]
lemma candidates_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : candidates (ctxBits distance F R H G)=
      encode ((CanonicalLengthView.candidates R H G).map planBits) := by
  simp only [candidates,frees_pack,paids_pack,CanonicalLengthView.candidates,List.map_append,encode_append]
noncomputable def view (x : List Bool) : List Bool := Find.run accepts (pairBits (x,candidates x))
noncomputable def view_computes : PolyComputes view :=
  (id_computes.pair candidates_computes).comp (Find.run_computes accepts_computes)
lemma view_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : view (ctxBits distance F R H G)=
      Find.optionEncode ((CanonicalLengthView.view (rows distance) F R H G).map planBits) := by
  simp only [view,candidates_pack,Find.run_encode,List.find?_map,Function.comp_def,accepts_pack,CanonicalLengthView.view]
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
