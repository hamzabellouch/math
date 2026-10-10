import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.Clipped
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack10
import OAI.Combinatorics.KMedianRecovery.Recovery.FnProdEnum
import OAI.Combinatorics.KMedianRecovery.Encoding.NatWords

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRawOpening
open WordOperations BinaryArithmetic WordList RationalLinearFeasibility RationalOpenability EffectiveOpenability
open BinaryOpeningPayment BinaryOpeningEnumeration
lemma columns_source {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : columns (pack distances F W v z lam eta i)=
      encode (List.ofFn (fun j=>BinaryOpeningCoefficient.variableWord (variableEnum d F j))) := by
  rw [columns_pack,ofFn_variableEnum]

noncomputable def rowInput (x : List Bool) : List Bool := pairBits (x,columns (extractPrefix x))
noncomputable def rowInput_computes : PolyComputes rowInput := by
  have computation := id_computes.pair (extractPrefix_computes.comp columns_computes)
  exact computation
noncomputable def rowCoefficients (x : List Bool) : List Bool :=
  mapWith (fun y=>BinaryRational.encode (BinaryOpeningCoefficient.coefficient y)) (rowInput x)
noncomputable def rowCoefficients_computes : PolyComputes rowCoefficients := by
  have computation := rowInput_computes.comp (mapWith_computes BinaryOpeningCoefficient.coefficient_computes)
  unfold rowCoefficients
  simpa only [Function.comp_def] using computation
lemma rowCoefficients_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) :
    rowCoefficients (pairBits (pack distances F W v z lam eta i,BinaryOpeningConstant.kindWord r))=
      RationalMatrix.rowEncode (fun j=>(forms distances F W v z lam eta i r).coeff (variableEnum d F j)) := by
  simp only [rowCoefficients,rowInput,extractPrefix_pairBits,columns_source,mapWith_ofFn,
    BinaryOpeningCoefficient.coefficient_source,RationalMatrix.rowEncode,RationalArray.encode,List.map_ofFn,Function.comp_def]
noncomputable def rowWord (x : List Bool) : List Bool :=
  pairBits (rowCoefficients x,BinaryRational.encode (-BinaryOpeningConstant.constant x))
noncomputable def rowWord_computes : PolyComputes rowWord :=
  rowCoefficients_computes.pair (RatOps.neg BinaryOpeningConstant.constant_computes)
lemma rowWord_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) :
    rowWord (pairBits (pack distances F W v z lam eta i,BinaryOpeningConstant.kindWord r))=
      BinaryRow.encode ((forms distances F W v z lam eta i r).enumeratedRow (variableEnum d F)) := by
  simp only [rowWord,rowCoefficients_pack,BinaryOpeningConstant.constant_source,BinaryRow.encode,Form.enumeratedRow]
noncomputable def rows (x : List Bool) : List Bool := mapWith rowWord (pairBits (x,kinds x))
noncomputable def rows_computes : PolyComputes rows := by
  have computation := (id_computes.pair kinds_computes).comp (mapWith_computes rowWord_computes)
  unfold rows
  simpa only [Function.comp_def, id_eq] using computation
lemma rows_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : rows (pack distances F W v z lam eta i)=
      BinaryRow.rowsEncode ((kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).map
        (fun r=>(forms distances F W v z lam eta i r).enumeratedRow (variableEnum d F))) := by
  simp only [rows,kinds_pack,mapWith_encode,List.map_map,Function.comp_def,rowWord_pack,BinaryRow.rowsEncode]
noncomputable def bound (x : List Bool) : ℚ :=
  (1+BinaryRational.decode (field 2 x)*BinaryRational.decode (field 2 x))*BinaryRational.decode (field 3 x)
noncomputable def bound_computes : PolyComputes (fun x=>BinaryRational.encode (bound x)) :=
  RatOps.mul (RatOps.add (RatOps.const 1) (RatOps.mul (RatOps.ofWords (field_computes 2))
    (RatOps.ofWords (field_computes 2)))) (RatOps.ofWords (field_computes 3))
lemma bound_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : bound (pack distances F W v z lam eta i)=(1+v^2)*z := by
  simp only [bound,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRational.decode_encode,pow_two]
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (Count.run (columns x),pairBits (Count.run (kinds x),pairBits ((⌈bound x⌉₊).bits,rows x)))
noncomputable def prepared_computes : PolyComputes prepared :=
  (columns_computes.comp Count.run_computes).pair
    ((kinds_computes.comp Count.run_computes).pair ((RatOps.natCeil bound_computes).pair rows_computes))
lemma prepared_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : prepared (pack distances F W v z lam eta i)=
      BinaryOpeningOracle.pack distances F W v z lam eta i := by
  simp only [prepared,columns_source,kinds_pack,bound_pack,rows_pack,Count.run_encode,List.length_ofFn,
    List.length_map,BinaryOpeningOracle.pack,BinaryRationalDecision.pack]

noncomputable def run : List Bool → List Bool := BinaryExactSolve.run ∘ prepared
noncomputable def run_computes : PolyComputes run := prepared_computes.comp BinaryExactSolve.run_computes
lemma run_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : run (pack distances F W v z lam eta i)=
      BinaryOpeningOracle.resultBits F (storedOpening distances F W v z lam eta i) := by
  rw [run,Function.comp_apply,prepared_pack,BinaryOpeningOracle.run_eq]
lemma nil_iff {m d : ℕ} [PseudoMetricSpace (Fin m)] (loc : Fin d → Fin m)
    (distances : Fin m → Fin d → ℚ) (hd : ∀ f j,(distances f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) :
    run (pack distances F W v z lam eta i)=[] ↔
      ¬etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i := by
  rw [run,Function.comp_apply,prepared_pack]
  exact BinaryOpeningOracle.nil_iff loc distances hd F W v z lam eta i hv hv1 hz
lemma witness {m d : ℕ} [PseudoMetricSpace (Fin m)] (loc : Fin d → Fin m)
    (distances : Fin m → Fin d → ℚ) (hd : ∀ f j,(distances f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (h : run (pack distances F W v z lam eta i)≠[]) :
    ∃ x : Variables (Fin d) F → ℚ,
      run (pack distances F W v z lam eta i)=BinaryOpeningOracle.resultBits F (some x) ∧
      OpenabilityLinearization.Feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i
        (fun j=>(x (.inl j):ℝ)) (fun f a j=>(x (.inr (f,a,j)):ℝ)) := by
  rw [run,Function.comp_apply,prepared_pack] at h ⊢
  exact BinaryOpeningOracle.witness loc distances hd F W v z lam eta i h
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

noncomputable def natEq (x : List Bool) : Bool := decide (value (extractPrefix x)=value (discardPrefix x))
noncomputable def natEq_computes : PolyComputes (fun x=>[natEq x]) := by
  have h := (NatOps.le extractPrefix_computes discardPrefix_computes).cond
    (NatOps.le discardPrefix_computes extractPrefix_computes) (const_computes [false])
  convert h using 1
  funext x
  by_cases hl : value (extractPrefix x)≤value (discardPrefix x)
  · by_cases hr : value (discardPrefix x)≤value (extractPrefix x)
    · simp [natEq,le_antisymm hl hr]
    · have hn : value (extractPrefix x)≠value (discardPrefix x) := fun he=>hr (he ▸ le_rfl)
      simp [natEq,hl,hr,hn]
  · have hn : value (extractPrefix x)≠value (discardPrefix x) := fun he=>hl (he ▸ le_rfl)
    simp [natEq,hl,hn]

noncomputable def contains (x : List Bool) : Bool := decide (Find.run natEq x≠[])
noncomputable def contains_computes : PolyComputes (fun x=>[contains x]) := by
  have h := ((Find.run_computes natEq_computes).comp isEmpty_computes).cond
    (const_computes [false]) (const_computes [true])
  convert h using 1
  funext x
  by_cases hx : Find.run natEq x=[] <;> simp [contains,hx]
lemma contains_indices {m : ℕ} (i : Fin m) (fs : List (Fin m)) :
    contains (pairBits (i.val.bits,BinaryOpeningActivity.indices fs))=decide (i∈fs) := by
  simp only [contains,BinaryOpeningActivity.indices,Find.run_encode]
  apply decide_eq_decide.mpr
  simp only [ne_eq,BinaryOpeningActivity.optionEncode_nil_iff,List.find?_eq_none]
  simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,natEq,
    extractPrefix_pairBits,discardPrefix_pairBits,value_bits,decide_eq_true_eq,← Fin.ext_iff]
  simp only [not_forall,exists_prop,not_not]
  exact ⟨fun ⟨j,hj,he⟩=>he ▸ hj,fun hi=>⟨i,hi,rfl⟩⟩

def context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) : List Bool := encode [Rectangular.encode distance,
      BinaryOpeningActivity.indices ((subtypeList W).map Subtype.val),BinaryRational.encode v,
      BinaryRational.encode z,BinaryRational.encode lam,BinaryRational.encode 0,[],
      List.replicate d true,BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val)]
def query (x : List Bool) : List Bool := encode [itemField 0 x,itemField 1 x,itemField 2 x,
  itemField 3 x,itemField 4 x,itemField 5 x,discardPrefix x,itemField 7 x,itemField 8 x]
noncomputable def query_computes : PolyComputes query := by
  exact cons_computes (itemField_computes 0) (cons_computes (itemField_computes 1)
    (cons_computes (itemField_computes 2) (cons_computes (itemField_computes 3)
    (cons_computes (itemField_computes 4) (cons_computes (itemField_computes 5)
    (cons_computes discardPrefix_computes (cons_computes (itemField_computes 7)
    (cons_computes (itemField_computes 8) (const_computes [])))))))))
lemma query_context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (i : Fin m) : query (pairBits (context distance F W v z lam,i.val.bits))=
      pack distance F W v z lam 0 i := by
  simp only [query,itemField,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,pack]

noncomputable def answer : List Bool → List Bool := BinaryRawOpening.run ∘ query
noncomputable def answer_computes : PolyComputes answer := query_computes.comp BinaryRawOpening.run_computes
noncomputable def eligible (x : List Bool) : Bool :=
  if contains (pairBits (discardPrefix x,itemField 8 x)) then
    if contains (pairBits (discardPrefix x,itemField 1 x)) then false else decide (answer x≠[]) else false
noncomputable def eligible_computes : PolyComputes (fun x=>[eligible x]) := by
  have ha := (answer_computes.comp isEmpty_computes).cond (const_computes [false]) (const_computes [true])
  have h := ((discardPrefix_computes.pair (itemField_computes 8)).comp contains_computes).cond
    (((discardPrefix_computes.pair (itemField_computes 1)).comp contains_computes).cond
      (const_computes [false]) ha) (const_computes [false])
  convert h using 1
  funext x
  cases hF : contains (pairBits (discardPrefix x,itemField 8 x)) <;>
    cases hW : contains (pairBits (discardPrefix x,itemField 1 x)) <;>
      by_cases ha : answer x=[] <;> simp [eligible,hF,hW,ha]
lemma contains_finset {m : ℕ} (i : Fin m) (F : Finset (Fin m)) :
    contains (pairBits (i.val.bits,BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val)))=decide (i∈F) := by
  rw [contains_indices]
  apply decide_eq_decide.mpr
  simp only [List.mem_map]
  exact ⟨fun ⟨j,_,hj⟩=>hj ▸ j.property,fun hi=>⟨⟨i,hi⟩,mem_subtypeList F _,rfl⟩⟩
lemma eligible_context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (i : Fin m) : eligible (pairBits (context distance F W v z lam,i.val.bits))=
      decide (i∈F ∧ i∉W ∧ storedOpening distance F W v z lam 0 i≠none) := by
  unfold eligible
  have ha : answer (pairBits (context distance F W v z lam,i.val.bits))=
      BinaryOpeningOracle.resultBits F (storedOpening distance F W v z lam 0 i) := by
    rw [answer,Function.comp_apply,query_context,BinaryRawOpening.run_pack]
  rw [ha]
  simp only [itemField,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    contains_finset,decide_eq_true_eq]
  split_ifs <;> simp_all [BinaryOpeningOracle.resultBits_eq_nil_iff]

noncomputable def chosen : List Bool → List Bool := Find.run eligible
noncomputable def chosen_computes : PolyComputes chosen := Find.run_computes eligible_computes
noncomputable def chosenQuery (x : List Bool) : List Bool := pairBits (extractPrefix x,(chosen x).tail)
noncomputable def chosenQuery_computes : PolyComputes chosenQuery :=
  extractPrefix_computes.pair (chosen_computes.comp WordOperations.tail_computes)

noncomputable def bids (x : List Bool) : List Bool :=
  mapWith (Lookup.run ∘ RationalMatrix.swapWords) (pairBits ((answer x).tail,BinaryOpeningEnumeration.clients (extractPrefix x)))
noncomputable def bids_computes : PolyComputes bids := by
  have computation := ((answer_computes.comp WordOperations.tail_computes).pair
    (extractPrefix_computes.comp BinaryOpeningEnumeration.clients_computes)).comp
      (mapWith_computes (RationalMatrix.swapWords_computes.comp Lookup.run_computes))
  unfold bids
  simpa only [Function.comp_def] using computation
lemma enum_bid {m d : ℕ} (F : Finset (Fin m)) (j : Fin d) :
    variableEnum d F (Fin.castAdd (F.card*(d*d)) j)=Sum.inl j := by
  simp [variableEnum]
lemma bids_context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (i : Fin m) (a : Variables (Fin d) F → ℚ)
    (ha : storedOpening distance F W v z lam 0 i=some a) :
    bids (pairBits (context distance F W v z lam,i.val.bits))=
      RationalMatrix.rowEncode (fun j=>a (.inl j)) := by
  have hc : BinaryOpeningEnumeration.clients (context distance F W v z lam)=
      encode (List.ofFn (fun j : Fin d=>j.val.bits)) := by
    simp only [BinaryOpeningEnumeration.clients,Function.comp_apply,context,field_encode,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryEllipsoidInitial.indices_replicate]
  simp only [bids,answer,Function.comp_apply,query_context,BinaryRawOpening.run_pack,ha,
    BinaryOpeningOracle.resultBits,List.tail_cons,extractPrefix_pairBits,hc,mapWith_ofFn,
    RationalMatrix.swapWords,discardPrefix_pairBits,extractPrefix_pairBits]
  simp only [RationalMatrix.rowEncode_eq]
  congr 1
  apply congrArg List.ofFn
  funext j
  change Lookup.run (pairBits ((Fin.castAdd (F.card*(d*d)) j).val.bits,
    encode (List.ofFn (fun k=>BinaryRational.encode (a (variableEnum d F k))))))=BinaryRational.encode (a (.inl j))
  rw [lookup_ofFn,enum_bid]

def eventBits {m d : ℕ} (e : RationalPhase.Event m d) : List Bool :=
  pairBits (e.facility.val.bits,RationalMatrix.rowEncode (fun j=>e.bid[j]))
def resultBits {m d : ℕ} : Option (RationalPhase.Event m d) → List Bool
  | none=>[]
  | some e=>true::eventBits e
noncomputable def run (x : List Bool) : List Bool :=
  if chosen x=[] then [] else true::pairBits ((chosen x).tail,bids (chosenQuery x))
noncomputable def run_computes : PolyComputes run :=
  by
  have h := (chosen_computes.comp isEmpty_computes).cond (const_computes [])
    (((chosen_computes.comp WordOperations.tail_computes).pair (chosenQuery_computes.comp bids_computes)).comp
      (prefix_computes true))
  change PolyComputes (fun x=>if chosen x=[] then [] else true::pairBits ((chosen x).tail,bids (chosenQuery x)))
  simpa only [decide_eq_true_eq,Function.comp_def] using h

lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (todo : List (Fin m)) :
    run (pairBits (context distance F W v z lam,BinaryOpeningActivity.indices todo))=
      resultBits (RationalPhase.first distance F W v z lam todo) := by
  have chooseEq (todo : List (Fin m)) : chosen (pairBits (context distance F W v z lam,
      BinaryOpeningActivity.indices todo))=Find.optionEncode
        ((todo.find? (fun i=>decide (i∈F ∧ i∉W ∧ storedOpening distance F W v z lam 0 i≠none))).map (fun i=>i.val.bits)) := by
    simp only [chosen,BinaryOpeningActivity.indices,Find.run_encode,List.find?_map,Function.comp_def,eligible_context]
  induction todo with
  | nil=>simp [run,chooseEq,resultBits,RationalPhase.first,Find.optionEncode]
  | cons i todo ih=>
    by_cases hi : i∈F ∧ i∉W
    · cases ha : storedOpening distance F W v z lam 0 i with
      | none=>
        simp only [RationalPhase.first,ite_eq_left hi,ha] at ⊢
        rw [← ih]
        simp only [run,chosenQuery,chooseEq]
        simp only [List.find?_cons,ha,ne_eq,not_true_eq_false,and_false,decide_false]
        simp only [extractPrefix_pairBits]
      | some a=>
        have he : chosen (pairBits (context distance F W v z lam,BinaryOpeningActivity.indices (i::todo)))=true::i.val.bits := by
          rw [chooseEq]
          simp [hi.1,hi.2,ha,Find.optionEncode]
        simp only [run,he,List.cons_ne_nil,ite_false,List.tail_cons,chosenQuery,extractPrefix_pairBits,
          bids_context distance F W v z lam i a ha,RationalPhase.first,ite_eq_left hi,ha,resultBits,eventBits,
          Fin.getElem_fin,Vector.getElem_ofFn]
    · simp only [RationalPhase.first,ite_eq_right hi]
      rw [← ih]
      simp only [run,chosenQuery,chooseEq,extractPrefix_pairBits]
      have hf : ¬(i∈F ∧ i∉W ∧ storedOpening distance F W v z lam 0 i≠none) := fun h=>hi ⟨h.1,h.2.1⟩
      simp only [List.find?_cons,decide_eq_false hf]
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
