import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Entry
import OAI.Combinatorics.KMedianRecovery.Strictness.BidBound

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability

lemma finish_phase {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) : (finish distance F v lam q s).1.phase=s.phase := by
  induction q generalizing s with
  | zero=>rfl
  | succ q ih=>
    cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i)) with
    | none=>simp only [finish,he]
    | some e=>simp only [finish,he,ih,update]
lemma run_phase {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) : (run distance F v lam q s).1.phase=(1+v^2)^q*s.phase := by
  induction q generalizing s with
  | zero=>simp only [run,pow_zero,one_mul]
  | succ q ih=>
    simp only [run,ih,advance,finish_phase,pow_succ]
    ring
end MetricKMedianRecovery.RationalPhase
namespace MetricKMedianRecovery.BitMachine.BinaryPhaseCount
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment
attribute [local irreducible] WordList.map WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run BinaryPhaseRun.run
noncomputable def powerInput (x : List Bool) : List Bool := pairBits
  (encode [[],[],x,BinaryRational.encode 1,BinaryRational.encode 0,BinaryRational.encode 0,[],[],[]],[])
noncomputable def powerInput_computes : PolyComputes powerInput :=
  (list_computes [(fun _=>[]),(fun _=>[]),id,(fun _=>BinaryRational.encode 1),
    (fun _=>BinaryRational.encode 0),(fun _=>BinaryRational.encode 0),(fun _=>[]),(fun _=>[]),(fun _=>[])] (by
      intro f hf
      refine Classical.choice ?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first | exact ⟨id_computes⟩ | exact ⟨const_computes _⟩)).pair (const_computes [])
def dummy (_v : ℚ) : State 0 0 := ⟨∅,1,Vector.replicate 0 0⟩
lemma powerInput_pack (v : ℚ) : powerInput (BinaryRational.encode v)=
    stateBits (fun i : Fin 0=>i.elim0) ∅ v 0 (dummy v) := by
  simp only [powerInput,stateBits,dummy,BinaryPhaseFirst.context,Rectangular.encode,
    List.ofFn_zero,BinaryOpeningActivity.indices,subtypeList,Finset.card_empty,List.map_nil,
    encode,RationalMatrix.rowEncode_eq,List.replicate_zero]
noncomputable def power (x : List Bool) : List Bool := BinaryPhaseAdvance.sf 3
  (BinaryPhaseRun.run (pairBits (extractPrefix x,powerInput (discardPrefix x))))
noncomputable def power_computes : PolyComputes power :=
  ((extractPrefix_computes.pair (discardPrefix_computes.comp powerInput_computes)).comp BinaryPhaseRun.run_computes).comp
    (BinaryPhaseAdvance.sf_computes 3)
lemma phase_field {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : BinaryPhaseAdvance.sf 3 (stateBits distance F v lam s)=BinaryRational.encode s.phase := by
  simp only [BinaryPhaseAdvance.sf,Function.comp_apply,stateBits,extractPrefix_pairBits,BinaryPhaseFirst.context,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma power_pack (v : ℚ) (q : ℕ) : power (pairBits (List.replicate q true,BinaryRational.encode v))=
    BinaryRational.encode ((1+v^2)^q) := by
  simp only [power,extractPrefix_pairBits,discardPrefix_pairBits,powerInput_pack,BinaryPhaseRun.run_pack,
    phase_field,run_phase,dummy,mul_one]
noncomputable def cf (k : ℕ) : List Bool → List Bool := field k ∘ extractPrefix
noncomputable def cf_computes (k : ℕ) : PolyComputes (cf k) := extractPrefix_computes.comp (field_computes k)
noncomputable def contextAt (x : List Bool) : List Bool := encode
  [cf 0 x,cf 1 x,cf 2 x,discardPrefix x,cf 4 x,cf 5 x,cf 6 x,cf 7 x,cf 8 x]
noncomputable def contextAt_computes : PolyComputes contextAt :=
  list_computes [cf 0,cf 1,cf 2,discardPrefix,cf 4,cf 5,cf 6,cf 7,cf 8] (by
    intro f hf
    refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨cf_computes _⟩ | exact ⟨discardPrefix_computes⟩)
lemma contextAt_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam w : ℚ) : contextAt (pairBits (BinaryPhaseFirst.context distance F Q v z lam,BinaryRational.encode w))=
      BinaryPhaseFirst.context distance F Q v w lam := by
  simp only [contextAt,cf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
noncomputable def zeroBudget : List Bool → List Bool :=
  WordList.map (fun _=>BinaryRational.encode 0) ∘ BinaryOpeningEnumeration.clients
noncomputable def zeroBudget_computes : PolyComputes zeroBudget :=
  BinaryOpeningEnumeration.clients_computes.comp (map_computes (const_computes (BinaryRational.encode 0)))
lemma zeroBudget_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam : ℚ) : zeroBudget (BinaryPhaseFirst.context distance F Q v z lam)=
      RationalMatrix.rowEncode (fun _ : Fin d=>(0:ℚ)) := by
  simp only [zeroBudget,Function.comp_apply,BinaryOpeningEnumeration.clients,BinaryPhaseFirst.context,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryEllipsoidInitial.indices_replicate,
    map_encode,List.map_ofFn,RationalMatrix.rowEncode_eq]
  rfl
noncomputable def start (x : List Bool) : List Bool :=
  pairBits (contextAt x,zeroBudget (extractPrefix x))
noncomputable def start_computes : PolyComputes start := contextAt_computes.pair (extractPrefix_computes.comp zeroBudget_computes)
lemma start_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam w : ℚ) : start (pairBits (BinaryPhaseFirst.context distance F Q v z lam,BinaryRational.encode w))=
      stateBits distance F v lam ⟨Q,w,Vector.replicate d 0⟩ := by
  rw [start,contextAt_pack,extractPrefix_pairBits,zeroBudget_pack]
  simp only [stateBits,Fin.getElem_fin,Vector.getElem_replicate]
noncomputable def included (x : List Bool) : Bool := BinaryPhaseFirst.contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def included_computes : PolyComputes (fun x=>[included x]) :=
  (discardPrefix_computes.pair extractPrefix_computes).comp BinaryPhaseFirst.contains_computes
noncomputable def regularOpened (x : List Bool) : List Bool :=
  Count.run (filterWith included (pairBits (BinaryPhaseAdvance.sf 8 x,BinaryPhaseAdvance.sf 1 x)))
noncomputable def regularOpened_computes : PolyComputes regularOpened :=
  (((BinaryPhaseAdvance.sf_computes 8).pair (BinaryPhaseAdvance.sf_computes 1)).comp
    (filterWith_computes included_computes)).comp Count.run_computes
lemma regularOpened_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : regularOpened (stateBits distance F v lam s)=List.replicate (s.opened∩F).card true := by
  have hi (i : Fin m) : included (pairBits
      (BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val),i.val.bits))=decide (i∈F) := by
    simp only [included,discardPrefix_pairBits,extractPrefix_pairBits,BinaryPhaseFirst.contains_finset]
  simp only [regularOpened,BinaryPhaseAdvance.sf,Function.comp_apply,stateBits,extractPrefix_pairBits,
    BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [show BinaryOpeningActivity.indices ((subtypeList s.opened).map Subtype.val)=
    encode (((subtypeList s.opened).map Subtype.val).map (fun i=>i.val.bits)) from rfl,filterWith_encode]
  rw [List.filter_map]
  simp only [Function.comp_def,hi]
  rw [Count.run_encode,List.length_map]
  have hf : (((subtypeList s.opened).map Subtype.val).filter (fun i=>decide (i∈F)))=
      (subtypeList (s.opened∩F)).map Subtype.val := by
    rw [←BinaryFiniteInsert.canonical_list,←BinaryFiniteInsert.canonical_list,List.filter_filter]
    congr 1
    funext i
    by_cases h₁ : i∈s.opened <;> by_cases h₂ : i∈F <;> simp [h₁,h₂]
  rw [hf,List.length_map,subtypeList_length]
noncomputable def prepare (x : List Bool) : List Bool := start
  (pairBits (discardPrefix x,power (pairBits (extractPrefix x,field 2 (discardPrefix x)))))
noncomputable def prepare_computes : PolyComputes prepare :=
  (discardPrefix_computes.pair ((extractPrefix_computes.pair (discardPrefix_computes.comp (field_computes 2))).comp
    power_computes)).comp start_computes
lemma prepare_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam : ℚ) (q : ℕ) : prepare (pairBits (List.replicate q true,BinaryPhaseFirst.context distance F Q v z lam))=
      stateBits distance F v lam ⟨Q,(1+v^2)^q,Vector.replicate d 0⟩ := by
  have hv : field 2 (BinaryPhaseFirst.context distance F Q v z lam)=BinaryRational.encode v := by
    simp only [BinaryPhaseFirst.context,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  simp only [prepare,extractPrefix_pairBits,discardPrefix_pairBits,hv,power_pack,start_pack]
noncomputable def run (x : List Bool) : List Bool := regularOpened
  (BinaryPhaseRun.run (pairBits (extractPrefix x,prepare (discardPrefix x))))
noncomputable def run_computes : PolyComputes run :=
  ((extractPrefix_computes.pair (discardPrefix_computes.comp prepare_computes)).comp BinaryPhaseRun.run_computes).comp
    regularOpened_computes
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam : ℚ) (q n : ℕ) :
    run (pairBits (List.replicate n true,pairBits (List.replicate q true,BinaryPhaseFirst.context distance F Q v z lam)))=
      List.replicate (RationalPhase.count distance F Q v lam q n) true := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits,prepare_pack,BinaryPhaseRun.run_pack,regularOpened_pack,count]
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

end OAI
