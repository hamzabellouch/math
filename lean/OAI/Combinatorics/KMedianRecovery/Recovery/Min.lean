import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.StateBits

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic WordList
namespace RatOps
noncomputable def min {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>BinaryRational.encode (min (f x) (g x))) := by
  have hh := (le hf hg).cond hf hg
  simpa only [decide_eq_true_eq,min_def,apply_ite] using hh
end RatOps
namespace BinaryPhaseAdvance
open EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment

def sf (k : ℕ) : List Bool → List Bool := field k ∘ extractPrefix
noncomputable def sf_computes (k : ℕ) : PolyComputes (sf k) := extractPrefix_computes.comp (field_computes k)
def paramV (x : List Bool) : ℚ := BinaryRational.decode (sf 2 x)
def paramZ (x : List Bool) : ℚ := BinaryRational.decode (sf 3 x)
noncomputable def paramV_computes : PolyComputes (fun x=>BinaryRational.encode (paramV x)) := RatOps.ofWords (sf_computes 2)
noncomputable def paramZ_computes : PolyComputes (fun x=>BinaryRational.encode (paramZ x)) := RatOps.ofWords (sf_computes 3)
def phase (x : List Bool) : ℚ := (1+paramV x*paramV x)*paramZ x
noncomputable def phase_computes : PolyComputes (fun x=>BinaryRational.encode (phase x)) :=
  RatOps.mul (RatOps.add (RatOps.const 1) (RatOps.mul paramV_computes paramV_computes)) paramZ_computes
lemma parameters_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) :
    paramV (stateBits distance F v lam s)=v ∧ paramZ (stateBits distance F v lam s)=s.phase ∧
    phase (stateBits distance F v lam s)=(1+v^2)*s.phase := by
  simp only [paramV,paramZ,phase,sf,Function.comp_apply,stateBits,extractPrefix_pairBits,
    BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRational.decode_encode,pow_two,and_self]
def query (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),discardPrefix x)
noncomputable def query_computes : PolyComputes query := (extractPrefix_computes.comp extractPrefix_computes).pair discardPrefix_computes
lemma activityInput_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    BinaryOpeningPayment.activityInput (query (pairBits (stateBits distance F v lam s,j.val.bits)))=
      pairBits (BinaryOpeningActivity.context distance v s.phase j,
        BinaryOpeningActivity.indices ((subtypeList s.opened).map Subtype.val)) := by
  simp only [BinaryOpeningPayment.activityInput,query,itemField,Function.comp_apply,stateBits,
    extractPrefix_pairBits,discardPrefix_pairBits,BinaryPhaseFirst.context,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryOpeningActivity.context]
noncomputable def isActive (x : List Bool) : Bool := BinaryOpeningPayment.active (query x)
noncomputable def isActive_computes : PolyComputes (fun x=>[isActive x]) := query_computes.comp BinaryOpeningPayment.active_computes
lemma isActive_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    isActive (pairBits (stateBits distance F v lam s,j.val.bits))=decide (EffectiveOpenability.active distance v s.phase s.opened j) := by
  simp only [isActive,BinaryOpeningPayment.active,activityInput_pack,BinaryOpeningActivity.run_source,
    List.head?_cons,Option.getD_some]
noncomputable def nearest (x : List Bool) : ℚ :=
  BinaryRational.decode (BinaryOpeningNearest.run (BinaryOpeningPayment.activityInput (query x)))
noncomputable def nearest_computes : PolyComputes (fun x=>BinaryRational.encode (nearest x)) := by
  have nearestComputes := RatOps.ofWords
    ((query_computes.comp BinaryOpeningPayment.activityInput_computes).comp BinaryOpeningNearest.run_computes)
  unfold nearest
  simpa only [Function.comp_def] using nearestComputes
lemma nearest_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    nearest (pairBits (stateBits distance F v lam s,j.val.bits))=RationalOpenability.nearest distance s.opened j := by
  simp only [nearest,activityInput_pack,BinaryOpeningNearest.run_source,BinaryRational.decode_encode]
lemma opened_nil {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : sf 1 (stateBits distance F v lam s)=[] ↔ ¬s.opened.Nonempty := by
  have hn (ws : List (List Bool)) : encode ws=[] ↔ ws=[] := by
    cases ws with
    | nil=>simp only [encode]
    | cons w ws=>simp only [encode,cons_ne_nil,List.cons_ne_nil]
  simp only [sf,Function.comp_apply,stateBits,extractPrefix_pairBits,BinaryPhaseFirst.context,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryOpeningActivity.indices,hn,
    ←List.length_eq_zero_iff,List.length_map,subtypeList,List.length_ofFn,
    Finset.not_nonempty_iff_eq_empty,Finset.card_eq_zero]
noncomputable def clippedItem (x : List Bool) : ℚ :=
  if sf 1 (extractPrefix x)=[] then phase (extractPrefix x)
  else min (phase (extractPrefix x)) ((1-3*paramV (extractPrefix x))*nearest x)
noncomputable def clippedItem_computes : PolyComputes (fun x=>BinaryRational.encode (clippedItem x)) := by
  have phaseComputes : PolyComputes
      (fun input=>BinaryRational.encode (phase (extractPrefix input))) := by
    simpa only [Function.comp_def] using (extractPrefix_computes.comp phase_computes)
  have paramVComputes : PolyComputes
      (fun input=>BinaryRational.encode (paramV (extractPrefix input))) := by
    simpa only [Function.comp_def] using (extractPrefix_computes.comp paramV_computes)
  have boundComputes := RatOps.mul
    (RatOps.sub (RatOps.const 1) (RatOps.mul (RatOps.const 3) paramVComputes)) nearest_computes
  have emptyComputes : PolyComputes (fun input=>[decide (sf 1 (extractPrefix input)=[])]) := by
    simpa only [Function.comp_def] using
      ((extractPrefix_computes.comp (sf_computes 1)).comp isEmpty_computes)
  have clippedComputes := emptyComputes.cond phaseComputes (RatOps.min phaseComputes boundComputes)
  unfold clippedItem
  simpa only [decide_eq_true_eq,apply_ite] using clippedComputes
lemma clippedItem_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    clippedItem (pairBits (stateBits distance F v lam s,j.val.bits))=
      clipped distance v ((1+v^2)*s.phase) s.opened j := by
  simp only [clippedItem,extractPrefix_pairBits,opened_nil,parameters_pack,nearest_pack,clipped]
  split_ifs <;> simp_all
noncomputable def budgetItem (x : List Bool) : List Bool :=
  if isActive x then BinaryRational.encode (clippedItem x)
  else Lookup.run (pairBits (discardPrefix x,discardPrefix (extractPrefix x)))
noncomputable def budgetItem_computes : PolyComputes budgetItem := isActive_computes.cond clippedItem_computes
  ((discardPrefix_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).comp Lookup.run_computes)
lemma budgetItem_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    budgetItem (pairBits (stateBits distance F v lam s,j.val.bits))=BinaryRational.encode (advance distance v s).budget[j] := by
  rw [budgetItem,isActive_pack,clippedItem_pack]
  simp only [stateBits,extractPrefix_pairBits,discardPrefix_pairBits,RationalMatrix.rowEncode_eq,lookup_ofFn,
    advance_get,decide_eq_true_eq,apply_ite]
  split_ifs <;> rfl
noncomputable def budget (x : List Bool) : List Bool :=
  mapWith budgetItem (pairBits (x,BinaryOpeningEnumeration.clients (extractPrefix x)))
noncomputable def budget_computes : PolyComputes budget := by
  have budgetComputes :=
    (id_computes.pair (extractPrefix_computes.comp BinaryOpeningEnumeration.clients_computes)).comp
      (mapWith_computes budgetItem_computes)
  unfold budget
  simpa only [Function.comp_def,id_eq] using budgetComputes
lemma budget_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : budget (stateBits distance F v lam s)=
      RationalMatrix.rowEncode (fun j=>(advance distance v s).budget[j]) := by
  have hc : BinaryOpeningEnumeration.clients (extractPrefix (stateBits distance F v lam s))=
      encode (List.ofFn (fun j : Fin d=>j.val.bits)) := by
    simp only [stateBits,extractPrefix_pairBits,BinaryOpeningEnumeration.clients,Function.comp_apply,
      BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      BinaryEllipsoidInitial.indices_replicate]
  simp only [budget,hc,mapWith_ofFn,budgetItem_pack,RationalMatrix.rowEncode_eq]
noncomputable def context (x : List Bool) : List Bool := encode [sf 0 x,sf 1 x,sf 2 x,BinaryRational.encode (phase x),
  sf 4 x,sf 5 x,sf 6 x,sf 7 x,sf 8 x]
noncomputable def context_computes : PolyComputes context :=
  cons_computes (sf_computes 0) (cons_computes (sf_computes 1) (cons_computes (sf_computes 2)
    (cons_computes phase_computes (cons_computes (sf_computes 4) (cons_computes (sf_computes 5)
    (cons_computes (sf_computes 6) (cons_computes (sf_computes 7) (cons_computes (sf_computes 8) (const_computes [])))))))))
lemma context_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : context (stateBits distance F v lam s)=
      BinaryPhaseFirst.context distance F s.opened v ((1+v^2)*s.phase) lam := by
  rw [context,(parameters_pack distance F v lam s).2.2]
  simp only [sf,Function.comp_apply,stateBits,extractPrefix_pairBits,BinaryPhaseFirst.context,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
noncomputable def run (x : List Bool) : List Bool := pairBits (context x,budget x)
noncomputable def run_computes : PolyComputes run := context_computes.pair budget_computes
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : run (stateBits distance F v lam s)=stateBits distance F v lam (advance distance v s) := by
  rw [run,context_pack,budget_pack]
  rfl
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
