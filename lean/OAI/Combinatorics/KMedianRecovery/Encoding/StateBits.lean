import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FilterItem

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase
open BinaryOpeningPayment

def stateBits {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : List Bool :=
  pairBits (BinaryPhaseFirst.context distance F s.opened v s.phase lam,
    RationalMatrix.rowEncode (fun j=>s.budget[j]))
def context : List Bool → List Bool := extractPrefix ∘ extractPrefix
def oldBudget : List Bool → List Bool := discardPrefix ∘ extractPrefix
def newFacility : List Bool → List Bool := extractPrefix ∘ discardPrefix
def newBudget : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def context_computes : PolyComputes context := extractPrefix_computes.comp extractPrefix_computes
noncomputable def oldBudget_computes : PolyComputes oldBudget := extractPrefix_computes.comp discardPrefix_computes
noncomputable def newFacility_computes : PolyComputes newFacility := discardPrefix_computes.comp extractPrefix_computes
noncomputable def newBudget_computes : PolyComputes newBudget := discardPrefix_computes.comp discardPrefix_computes
def ctxField (k : ℕ) : List Bool → List Bool := field k ∘ context
noncomputable def ctxField_computes (k : ℕ) : PolyComputes (ctxField k) := context_computes.comp (field_computes k)
noncomputable def allFacilities : List Bool → List Bool := Indices.run ∘ field 0
noncomputable def allFacilities_computes : PolyComputes allFacilities := (field_computes 0).comp Indices.run_computes
lemma allFacilities_context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) : allFacilities (BinaryPhaseFirst.context distance F W v z lam)=
      BinaryOpeningActivity.indices (List.ofFn (fun i : Fin m=>i)) := by
  simp only [allFacilities,Function.comp_apply,BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,
    Option.getD_some,Rectangular.encode,indices_ofFn,BinaryOpeningActivity.indices,List.map_ofFn,Function.comp_def]
noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteInsert.run
  (pairBits (pairBits (ctxField 1 x,newFacility x),allFacilities (context x)))
noncomputable def opened_computes : PolyComputes opened :=
  (((ctxField_computes 1).pair newFacility_computes).pair (context_computes.comp allFacilities_computes)).comp
    BinaryFiniteInsert.run_computes
lemma opened_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (e : Event m d) :
    opened (pairBits (stateBits distance F v lam s,BinaryPhaseFirst.eventBits e))=
      BinaryOpeningActivity.indices ((subtypeList (insert e.facility s.opened)).map Subtype.val) := by
  simp only [opened,ctxField,context,newFacility,Function.comp_apply,stateBits,BinaryPhaseFirst.eventBits,
    extractPrefix_pairBits,discardPrefix_pairBits,allFacilities_context]
  simp only [BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinaryFiniteInsert.run_pack s.opened e.facility
noncomputable def updatedContext (x : List Bool) : List Bool := encode [ctxField 0 x,opened x,ctxField 2 x,
  ctxField 3 x,ctxField 4 x,ctxField 5 x,ctxField 6 x,ctxField 7 x,ctxField 8 x]
noncomputable def updatedContext_computes : PolyComputes updatedContext :=
  cons_computes (ctxField_computes 0) (cons_computes opened_computes (cons_computes (ctxField_computes 2)
    (cons_computes (ctxField_computes 3) (cons_computes (ctxField_computes 4) (cons_computes (ctxField_computes 5)
    (cons_computes (ctxField_computes 6) (cons_computes (ctxField_computes 7)
    (cons_computes (ctxField_computes 8) (const_computes [])))))))))
lemma updatedContext_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (e : Event m d) :
    updatedContext (pairBits (stateBits distance F v lam s,BinaryPhaseFirst.eventBits e))=
      BinaryPhaseFirst.context distance F (insert e.facility s.opened) v s.phase lam := by
  rw [updatedContext,opened_pack]
  simp only [ctxField,context,Function.comp_apply,stateBits,
    extractPrefix_pairBits,BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

noncomputable def active (x : List Bool) : Bool := BinaryOpeningPayment.active (pairBits (context (extractPrefix x),discardPrefix x))
noncomputable def active_computes : PolyComputes (fun x=>[active x]) :=
  ((extractPrefix_computes.comp context_computes).pair discardPrefix_computes).comp BinaryOpeningPayment.active_computes
lemma active_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (e : Event m d) (j : Fin d) :
    active (pairBits (pairBits (stateBits distance F v lam s,BinaryPhaseFirst.eventBits e),j.val.bits))=
      decide (EffectiveOpenability.active distance v s.phase s.opened j) := by
  have he : BinaryOpeningPayment.activityInput (pairBits (BinaryPhaseFirst.context distance F s.opened v s.phase lam,j.val.bits))=
      BinaryOpeningPayment.activityInput (pairBits (pack distance F s.opened v s.phase lam 0 e.facility,j.val.bits)) := by
    simp only [BinaryOpeningPayment.activityInput,itemField,Function.comp_apply,extractPrefix_pairBits,
      discardPrefix_pairBits,BinaryPhaseFirst.context,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [active,context,Function.comp_apply,stateBits,extractPrefix_pairBits,discardPrefix_pairBits]
  change (BinaryOpeningActivity.run (BinaryOpeningPayment.activityInput (pairBits
    (BinaryPhaseFirst.context distance F s.opened v s.phase lam,j.val.bits)))).head?.getD false=_
  rw [he]
  exact BinaryOpeningPayment.active_pack distance F s.opened v s.phase lam 0 e.facility j
noncomputable def budgetItem (x : List Bool) : List Bool :=
  if active x then Lookup.run (pairBits (discardPrefix x,newBudget (extractPrefix x)))
  else Lookup.run (pairBits (discardPrefix x,oldBudget (extractPrefix x)))
noncomputable def budgetItem_computes : PolyComputes budgetItem := by
  have h := active_computes.cond
    ((discardPrefix_computes.pair (extractPrefix_computes.comp newBudget_computes)).comp Lookup.run_computes)
    ((discardPrefix_computes.pair (extractPrefix_computes.comp oldBudget_computes)).comp Lookup.run_computes)
  exact h
lemma budgetItem_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (e : Event m d) (j : Fin d) :
    budgetItem (pairBits (pairBits (stateBits distance F v lam s,BinaryPhaseFirst.eventBits e),j.val.bits))=
      BinaryRational.encode ((update distance v s e).budget[j]) := by
  rw [budgetItem,active_pack]
  simp only [newBudget,oldBudget,Function.comp_apply,stateBits,
    BinaryPhaseFirst.eventBits,extractPrefix_pairBits,discardPrefix_pairBits,RationalMatrix.rowEncode_eq,
    lookup_ofFn,update_get,decide_eq_true_eq,apply_ite]
  split_ifs <;> rfl
noncomputable def updatedBudget (x : List Bool) : List Bool :=
  mapWith budgetItem (pairBits (x,BinaryOpeningEnumeration.clients (context x)))
noncomputable def updatedBudget_computes : PolyComputes updatedBudget := by
  have computation := (id_computes.pair (context_computes.comp BinaryOpeningEnumeration.clients_computes)).comp
    (mapWith_computes budgetItem_computes)
  unfold updatedBudget
  simpa only [Function.comp_def, id_eq] using computation
lemma updatedBudget_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (e : Event m d) :
    updatedBudget (pairBits (stateBits distance F v lam s,BinaryPhaseFirst.eventBits e))=
      RationalMatrix.rowEncode (fun j=>(update distance v s e).budget[j]) := by
  have hc : BinaryOpeningEnumeration.clients (context (pairBits (stateBits distance F v lam s,BinaryPhaseFirst.eventBits e)))=
      encode (List.ofFn (fun j : Fin d=>j.val.bits)) := by
    simp only [context,Function.comp_apply,stateBits,extractPrefix_pairBits,BinaryOpeningEnumeration.clients,
      BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      BinaryEllipsoidInitial.indices_replicate]
  simp only [updatedBudget,hc,mapWith_ofFn,budgetItem_pack,RationalMatrix.rowEncode_eq]
noncomputable def run (x : List Bool) : List Bool := pairBits (updatedContext x,updatedBudget x)
noncomputable def run_computes : PolyComputes run := updatedContext_computes.pair updatedBudget_computes
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (e : Event m d) :
    run (pairBits (stateBits distance F v lam s,BinaryPhaseFirst.eventBits e))=
      stateBits distance F v lam (update distance v s e) := by
  rw [run,updatedContext_pack,updatedBudget_pack]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate

end OAI
