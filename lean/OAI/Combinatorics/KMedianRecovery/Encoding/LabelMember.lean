import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelOrder

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic WordList RationalLeaves

def eq (x : List Bool) : Bool :=
  decide (value (levelWords (extractPrefix x))=value (levelWords (discardPrefix x))) &&
    (decide (value (parentWords (extractPrefix x))=value (parentWords (discardPrefix x))) &&
      decide (BinaryRational.decode (heightWords (extractPrefix x))=BinaryRational.decode (heightWords (discardPrefix x))))
noncomputable def eq_computes : PolyComputes (fun x=>[eq x]) :=
  (NatOps.eq (extractPrefix_computes.comp levelWords_computes) (discardPrefix_computes.comp levelWords_computes)).and
    ((NatOps.eq (extractPrefix_computes.comp parentWords_computes) (discardPrefix_computes.comp parentWords_computes)).and
      (RatOps.eq (RatOps.ofWords (extractPrefix_computes.comp heightWords_computes))
        (RatOps.ofWords (discardPrefix_computes.comp heightWords_computes))))
lemma fields_injective {m : ℕ} (a b : Label (Fin m)) :
    level a=level b ∧ (parent a).val=(parent b).val ∧ rationalHeight a=rationalHeight b ↔ a=b := by
  cases a <;> cases b <;> simp [level,parent,root,rationalHeight,Fin.ext_iff,Prod.ext_iff]
lemma eq_pair {m : ℕ} (a b : Label (Fin m)) : eq (pairBits (encode a,encode b))=decide (a=b) := by
  simp only [eq,extractPrefix_pairBits,discardPrefix_pairBits,levelWords_encode,parentWords_encode,
    heightWords_encode,value_bits,BinaryRational.decode_encode,←Bool.decide_and,fields_injective]

noncomputable def contains (x : List Bool) : Bool := decide (Find.run eq x≠[])
noncomputable def contains_computes : PolyComputes (fun x=>[contains x]) := by
  have h := ((Find.run_computes eq_computes).comp isEmpty_computes).not
  simpa only [contains,←decide_not] using h
lemma contains_encode {m : ℕ} (a : Label (Fin m)) (xs : List (Label (Fin m))) :
    contains (pairBits (encode a,WordList.encode (xs.map encode)))=by classical exact decide (a∈xs) := by
  classical
  simp only [contains,Find.run_encode]
  apply decide_eq_decide.mpr
  simp only [ne_eq,BinaryOpeningActivity.optionEncode_nil_iff,List.find?_eq_none]
  simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,eq_pair,decide_eq_true_eq]
  simp only [not_forall,exists_prop,not_not]
  exact ⟨fun ⟨b,hb,he⟩=>he ▸ hb,fun ha=>⟨a,ha,rfl⟩⟩

theorem encode_injective {m : ℕ} : Function.Injective (@encode m) := by
  intro a b h
  have hq:=eq_pair a b
  rw [h,eq_pair b b] at hq
  exact of_decide_eq_true (by simpa only [decide_true] using hq.symm)

end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.EffectiveOpenability
lemma subtypeList_values {m : ℕ} (S : Finset (Fin m)) :
    (subtypeList S).map Subtype.val=S.sort (·≤·) := by
  rw [subtypeList,List.map_ofFn,List.ofFn_eq_map]
  exact Finset.listMap_orderEmbOfFin_finRange S rfl

lemma filter_finRange {m : ℕ} (S : Finset (Fin m)) :
    (List.finRange m).filter (·∈S)=(subtypeList S).map Subtype.val := by
  rw [subtypeList_values]
  apply List.Pairwise.eq_of_mem_iff (r:=(·<·))
  · exact (List.sortedLT_finRange m).pairwise.filter _
  · exact (Finset.sortedLT_sort S).pairwise
  · simp
end MetricKMedianRecovery.EffectiveOpenability

namespace MetricKMedianRecovery.BitMachine.WordList
lemma lookup_list {α : Type*} (E : α → List Bool) (xs : List α) (i : Fin xs.length) :
    Lookup.run (pairBits (i.val.bits,encode (xs.map E)))=E (xs.get i) := by
  rw [Lookup.run_encode]
  simp only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,Option.map_some,Option.getD_some,List.get_eq_getElem]
lemma indices_list {α : Type*} (E : α → List Bool) (xs : List α) :
    Indices.run (encode (xs.map E))=encode ((List.finRange xs.length).map (fun i=>i.val.bits)) := by
  rw [Indices.run_encode,List.length_map]
  congr 1
  rw [←List.map_coe_finRange_eq_range,List.map_map]
  rfl
end MetricKMedianRecovery.BitMachine.WordList

namespace MetricKMedianRecovery.BitMachine.BinaryLabelSelect
open Classical
open WordOperations BinaryArithmetic WordList RationalLeaves EffectiveOpenability

def alphabet : List Bool → List Bool := extractPrefix ∘ extractPrefix
def target : List Bool → List Bool := discardPrefix ∘ extractPrefix
def index : List Bool → List Bool := discardPrefix
noncomputable def alphabet_computes : PolyComputes alphabet := extractPrefix_computes.comp extractPrefix_computes
noncomputable def target_computes : PolyComputes target := extractPrefix_computes.comp discardPrefix_computes
noncomputable def index_computes : PolyComputes index := discardPrefix_computes
noncomputable def test (x : List Bool) : Bool :=
  BinaryLabel.contains (pairBits (Lookup.run (pairBits (index x,alphabet x)),target x))
noncomputable def test_computes : PolyComputes (fun x=>[test x]) :=
  (((index_computes.pair alphabet_computes).comp Lookup.run_computes).pair target_computes).comp
    BinaryLabel.contains_computes
lemma test_pack {m : ℕ} (xs ys : List (Label (Fin m))) (i : Fin xs.length) :
    test (pairBits (pairBits (encode (xs.map BinaryLabel.encode),encode (ys.map BinaryLabel.encode)),i.val.bits))=
      decide (xs.get i∈ys) := by
  simp only [test,index,alphabet,target,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    lookup_list,BinaryLabel.contains_encode]

noncomputable def run (x : List Bool) : List Bool :=
  filterWith test (pairBits (x,Indices.run (extractPrefix x)))
noncomputable def run_computes : PolyComputes run :=
  (id_computes.pair (extractPrefix_computes.comp Indices.run_computes)).comp (filterWith_computes test_computes)
lemma run_pack {m : ℕ} (xs ys : List (Label (Fin m))) :
    run (pairBits (encode (xs.map BinaryLabel.encode),encode (ys.map BinaryLabel.encode)))=
      BinaryOpeningActivity.indices ((subtypeList (Finset.univ.filter (fun i : Fin xs.length=>xs.get i∈ys))).map Subtype.val) := by
  simp only [run,extractPrefix_pairBits,indices_list,filterWith_encode,List.filter_map,Function.comp_def,test_pack]
  rw [show (fun i : Fin xs.length=>decide (xs.get i∈ys))=(fun i=>decide (i∈Finset.univ.filter (fun i : Fin xs.length=>xs.get i∈ys))) by
    funext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and]]
  rw [filter_finRange]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryLabelSelect

end OAI
