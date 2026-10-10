import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.FinSets
import OAI.Combinatorics.KMedianRecovery.Branching.BlueDPValue
import OAI.Combinatorics.KMedianRecovery.Encoding.WordSubsets

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L A : Type*} [LinearOrder L]
abbrev Table (L A : Type*) := List (Finset L × Candidate (List A))
def lookup (U : Finset L) : Table L A → Candidate (List A)
  | []=>none
  | (V,x)::xs=>if U=V then x else lookup U xs
lemma lookup_map (vs : List (Finset L)) (f : Finset L→Candidate (List A)) (U : Finset L) (h : U∈vs) :
    lookup U (vs.map (fun V=>(V,f V)))=f U := by
  induction vs with
  | nil=>simp at h
  | cons V vs ih=>
    simp only [List.map_cons,lookup]
    by_cases he : U=V
    · simp [he]
    · rw [ite_eq_right he]
      exact ih (List.mem_cons.mp h |>.resolve_left he)
def states (U : Finset L) : List (Finset L) := (U.sort (·≤·)).sublists.map List.toFinset
lemma mem_states (U V : Finset L) : V∈states U ↔ V⊆U := by
  simp only [states,List.mem_map,List.mem_sublists]
  constructor
  · rintro ⟨xs,hxs,rfl⟩
    intro l hl
    exact (Finset.mem_sort (·≤·)).mp (hxs.subset (List.mem_toFinset.mp hl))
  · intro h
    refine ⟨(U.sort (·≤·)).filter (fun l=>l∈V),List.filter_sublist,?_⟩
    ext l
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨And.right,fun hv=>⟨h hv,hv⟩⟩
lemma states_length (U : Finset L) : (states U).length=2^U.card := by
  simp [states,List.length_sublists]
def initialTable (U : Finset L) : Table L A := (states U).map (fun V=>(V,if V=∅ then some (0,[]) else none))
def nextTable (C : Finset L→Candidate (List A)) (U : Finset L) (T : Table L A) : Table L A :=
  (states U).map (fun W=>(W,select ((enumBlocks W).map (fun V=>merge (C V) (lookup (W\V) T)))))
def tables (C : Finset L→Candidate (List A)) (U : Finset L) : ℕ→Table L A
  | 0=>initialTable U
  | t+1=>nextTable C U (tables C U t)
lemma tables_eq (C : Finset L→Candidate (List A)) (U : Finset L) (t : ℕ) :
    tables C U t=(states U).map (fun V=>(V,recurrence C t V)) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    simp only [tables,nextTable,ih]
    apply List.map_congr_left
    intro W hW
    have hWU := (mem_states U W).mp hW
    congr 1
    conv_rhs => rw [recurrence]
    congr 1
    apply List.map_congr_left
    intro V _
    rw [lookup_map _ _ _ ((mem_states U (W\V)).mpr ((Finset.sdiff_subset).trans hWU))]
lemma lookup_tables (C : Finset L→Candidate (List A)) (U W : Finset L) (t : ℕ) (hW : W⊆U) :
    lookup W (tables C U t)=recurrence C t W := by
  rw [tables_eq,lookup_map _ _ _ ((mem_states U W).mpr hW)]
lemma tables_length (C : Finset L→Candidate (List A)) (U : Finset L) (t : ℕ) :
    (tables C U t).length=2^U.card := by
  rw [tables_eq,List.length_map,states_length]
def tableStep (C : Finset L→Candidate (List A)) (U : Finset L) (s : Table L A×Candidate (List A)) :
    Table L A×Candidate (List A) :=
  let T:=nextTable C U s.1
  (T,choose s.2 (lookup U T))
def tableRun (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) : Table L A×Candidate (List A) :=
  (tableStep C U)^[c] (initialTable U,none)
lemma tableRun_spec (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) :
    tableRun C U c=(tables C U c,select ((List.range c).map (fun t=>recurrence C (t+1) U))) := by
  induction c with
  | zero=>rfl
  | succ c ih=>
    rw [tableRun,Function.iterate_succ_apply']
    change tableStep C U (tableRun C U c)=_
    rw [ih]
    simp only [tableStep,show nextTable C U (tables C U c)=tables C U (c+1) from rfl,
      lookup_tables C U U (c+1) le_rfl,List.range_succ,List.map_append,
      List.map_singleton,select,List.foldl_append,List.foldl_cons,List.foldl_nil]
def tableBest (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) : Candidate (List A) :=
  if U=∅ then some (0,[]) else (tableRun C U c).2
lemma tableBest_eq (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) : tableBest C U c=best C c U := by
  simp only [tableBest,tableRun_spec,best]
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordOperations WordList
variable {n : ℕ}
lemma key_sublist (U : Finset (Fin n)) (xs : List (Fin n)) (h : xs.Sublist (U.sort (·≤·))) :
    BinaryFinSet.encode xs.toFinset=WordList.encode (xs.map (fun i=>i.val.bits)) := by
  rw [BinaryFinSet.encode_eq,(List.toFinset_sort (r:=(·≤·)) (List.Nodup.sublist h (Finset.sort_nodup U (·≤·)))).mpr
    (List.Pairwise.sublist h (Finset.pairwise_sort U (·≤·)))]
lemma states_encode (U : Finset (Fin n)) :
    WordList.encode ((BlueDP.states U).map BinaryFinSet.encode)=
      WordList.encode (((U.sort (·≤·)).map (fun i=>i.val.bits)).sublists.map WordList.encode) := by
  simp only [BlueDP.states,List.sublists_map,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro xs hx
  exact key_sublist U xs (List.mem_sublists.mp hx)
noncomputable def run (d : ℕ) : List Bool→List Bool := Subsets.run d
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) := Subsets.run_computes d
lemma run_pack (d : ℕ) (ctx : List Bool) (U : Finset (Fin n))
    (hb : 2^U.card*(2*(BinaryFinSet.encode U).length+2)≤((pairBits (ctx,BinaryFinSet.encode U)).length+1)^d) :
    run d (pairBits (ctx,BinaryFinSet.encode U))=WordList.encode ((BlueDP.states U).map BinaryFinSet.encode) := by
  rw [run,BinaryFinSet.encode_eq,Subsets.run_pack]
  · exact (states_encode U).symm
  · simpa only [List.length_map,Finset.length_sort,←BinaryFinSet.encode_eq] using hb
noncomputable def nonemptyKey (x : List Bool) : Bool := !decide (discardPrefix x=[])
noncomputable def nonemptyKey_computes : PolyComputes (fun x=>[nonemptyKey x]) := by
  simpa only [nonemptyKey,beq_iff_eq] using (discardPrefix_computes.comp isEmpty_computes).not
noncomputable def blocks (d : ℕ) (x : List Bool) : List Bool := filterWith nonemptyKey (pairBits ([],run d x))
noncomputable def blocks_computes (d : ℕ) : PolyComputes (blocks d) :=
  ((const_computes []).pair (run_computes d)).comp (filterWith_computes nonemptyKey_computes)
lemma key_empty (U : Finset (Fin n)) : BinaryFinSet.encode U=[] ↔ U=∅ := by
  constructor
  · intro he
    have hh:=WordList.length_le_encode ((U.sort (·≤·)).map (fun i=>i.val.bits))
    rw [←BinaryFinSet.encode_eq,he] at hh
    simp only [List.length_map,Finset.length_sort,List.length_nil] at hh
    exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
  · rintro rfl
    simp [BinaryFinSet.encode_eq,WordList.encode]
lemma nonemptyKey_pair (U : Finset (Fin n)) :
    nonemptyKey (pairBits ([],BinaryFinSet.encode U))=decide (U≠∅) := by
  simp [nonemptyKey,key_empty]
lemma blocks_pack (d : ℕ) (ctx : List Bool) (U : Finset (Fin n))
    (hb : 2^U.card*(2*(BinaryFinSet.encode U).length+2)≤((pairBits (ctx,BinaryFinSet.encode U)).length+1)^d) :
    blocks d (pairBits (ctx,BinaryFinSet.encode U))=WordList.encode ((BlueDP.enumBlocks U).map BinaryFinSet.encode) := by
  rw [blocks,run_pack d ctx U hb,filterWith_encode]
  simp only [List.filter_map,Function.comp_def,nonemptyKey_pair,BlueDP.enumBlocks,BlueDP.states]
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

end OAI
