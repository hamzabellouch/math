import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerUpdateParts

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField actionField_computes)
attribute [local irreducible] radius
variable {n : ℕ}
noncomputable def active (x : List Bool) : Bool := Weights.active (pairBits (Weights.context (extractPrefix x),[]))
noncomputable def active_computes : PolyComputes (fun x=>[active x]) :=
  (((extractPrefix_computes.comp Weights.context_computes).pair (const_computes [])).comp Weights.active_computes)
noncomputable def old (x : List Bool) : Bool := decide (value (chosen x)<value (c 0 (input x)))
noncomputable def old_computes : PolyComputes (fun x=>[old x]) := NatOps.lt chosen_computes (input_computes.comp (c_computes 0))
noncomputable def remove (x : List Bool) : List Bool := BinarySamplingState.retain (pairBits
  (c 8 (input x),BinarySamplingState.remove (pairBits (discardPrefix (input x),chosen x))))
noncomputable def remove_computes : PolyComputes remove :=
  ((input_computes.comp (c_computes 8)).pair (((input_computes.comp discardPrefix_computes).pair chosen_computes).comp
    BinarySamplingState.remove_computes)).comp BinarySamplingState.retain_computes
noncomputable def add (x : List Bool) : List Bool := BinarySamplingState.retain (pairBits
  (c 8 (input x),BinarySamplingState.add (pairBits (discardPrefix (input x),pairBits (actionField 1 x,WordList.head (radius x))))))
noncomputable def add_computes : PolyComputes add :=
  ((input_computes.comp (c_computes 8)).pair (((input_computes.comp discardPrefix_computes).pair
    ((actionField_computes 1).pair (radius_computes.comp WordList.head_computes))).comp BinarySamplingState.add_computes)).comp BinarySamplingState.retain_computes
noncomputable def run (x : List Bool) : List Bool :=
  if active x then if Weights.kind 0 x then [] else if Weights.kind 1 x then
    if old x then remove x else []
  else if radius x=[] then [] else if ball x=[] then [] else add x
  else []
noncomputable def run_computes : PolyComputes run := by
  have hh := active_computes.cond ((Weights.kind_computes 0).cond (const_computes [])
    ((Weights.kind_computes 1).cond (old_computes.cond remove_computes (const_computes []))
      ((radius_computes.comp isEmpty_computes).cond (const_computes [])
        ((ball_computes.comp isEmpty_computes).cond (const_computes []) add_computes)))) (const_computes [])
  convert hh using 1
  funext x
  simp only [run,decide_eq_true_eq]
lemma context_some (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) :
    Weights.context (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)))=
      encode [BinarySamplingOracle.pack δ D S Δ s,BinaryRational.encode (RationalSampling.totalWeight δ D S Δ s),BinaryMenu.weights M E J,
        BinarySamplingState.optionBits (some s)] := by
  rw [Weights.context,Weights.stateInput_some,oracle_pair,BinarySamplingOracle.total_pack]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,discardPrefix_pairBits]
lemma active_none (cfg ac : List Bool) : active (pairBits (pairBits (cfg,BinarySamplingState.optionBits (n:=n) none),ac))=false := by
  simp only [active,Weights.active,Weights.context,extractPrefix_pairBits,discardPrefix_pairBits,c,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Weights.state_none,decide_true,Bool.not_true,Bool.false_and]
lemma active_some (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (ac : List Bool) :
    active (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),ac))=
      decide (0<RationalSampling.totalWeight δ D S Δ s) := by
  simp only [active,extractPrefix_pairBits,context_some,Weights.active,c,extractPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Weights.state_some_ne,decide_false,Bool.not_false,
    Bool.true_and,BinaryRational.decode_encode]
lemma old_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : D) :
    old (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))))=decide (RationalSampling.chosenId δ S Δ s w<n) := by
  rw [old,show RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))=RationalSampling.actionCode D M E J
    ((none : Option (Sampling.Entry M E J)).elim (Sum.inr (Sum.inl w)) (fun e=>Sum.inr (Sum.inr (w,e)))) from rfl,chosen_pair]
  simp only [input,extractPrefix_pairBits,Weights.stateInput_some,c,config,field_encode,List.getElem?_cons_zero,Option.getD_some,value_bits]
lemma remove_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : D)
    (h : RationalSampling.chosenId δ S Δ s w<n) :
    remove (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))))=
      BinarySamplingState.optionBits (RationalSampling.retain m (s.remove ⟨RationalSampling.chosenId δ S Δ s w,h⟩)) := by
  rw [remove,show RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))=RationalSampling.actionCode D M E J
    ((none : Option (Sampling.Entry M E J)).elim (Sum.inr (Sum.inl w)) (fun e=>Sum.inr (Sum.inr (w,e)))) from rfl,chosen_pair]
  simp only [input,extractPrefix_pairBits,Weights.stateInput_some,discardPrefix_pairBits,c,config,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  rw [show (RationalSampling.chosenId δ S Δ s w).bits=(⟨RationalSampling.chosenId δ S Δ s w,h⟩:Fin n).val.bits from rfl,
    BinarySamplingState.remove_pair,BinarySamplingState.retain_pair]
lemma add_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : D)
    (e : Sampling.Entry M E J) (R : ℚ) (hr : RationalSampling.menuRadius δ D P κ m M E J s w e=some R) :
    add (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=BinarySamplingState.optionBits (RationalSampling.retain m (s.add w R)) := by
  rw [add,radius_pair,hr]
  simp only [input,extractPrefix_pairBits,Weights.stateInput_some,discardPrefix_pairBits,actionField,RationalSampling.actionCode,
    field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryMenu.optBits,
    Option.toList_some,List.map_cons,List.map_nil]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  simp only [WordList.encode,WordList.head_cons]
  rw [show pairBits (w.val.val.bits,BinaryRational.encode R)=BinarySamplingReference.leafBits w.val R from rfl,
    BinarySamplingState.add_pair,BinarySamplingState.retain_pair]

end MetricKMedianRecovery.BitMachine.BinarySampler.Update

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma optionRadius_eq_nil (R : Option ℚ) : BinaryMenu.optBits R=[] ↔ R=none := by
  cases R with
  | none=>simp [BinaryMenu.optBits,encode]
  | some q=>simp [BinaryMenu.optBits,encode,WordList.cons]
lemma finset_eq_nil (F : Finset (Fin n)) : BinaryFinSet.encode F=[] ↔ ¬F.Nonempty := by
  have hh (xs : List (List Bool)) : encode xs=[] ↔ xs=[] := ⟨fun h=>encode_injective (show encode xs=encode [] from h),fun h=>by subst xs;rfl⟩
  rw [BinaryFinSet.encode_eq,hh]
  rw [List.map_eq_nil_iff,←List.length_eq_zero_iff,Finset.length_sort,Finset.card_eq_zero,Finset.not_nonempty_iff_eq_empty]
lemma run_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (RationalSampling.State n)) (a : Sampling.Action D M E J) :
    run (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits s),RationalSampling.actionCode D M E J a))=
      BinarySamplingState.optionBits (RationalSampling.update δ D F S Δ P κ m M E J s a) := by
  cases s with
  | none=>rw [run,active_none];rfl
  | some s=>
    rw [run,active_some]
    simp only [decide_eq_true_eq,RationalSampling.update]
    by_cases htot : 0<RationalSampling.totalWeight δ D S Δ s
    · rw [ite_eq_left htot,ite_eq_left htot]
      rcases a with u | (w | ⟨w,e⟩)
      · cases u
        simp only [Weights.kind,Weights.actionField,discardPrefix_pairBits,RationalSampling.actionCode,field_encode,
          List.getElem?_cons_zero,Option.getD_some,value_bits,decide_true,ite_true,Weights.state_none]
      · have hk0 : Weights.kind 0 (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
            RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))))=false := by
          norm_num [Weights.kind,Weights.actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,value_bits,value]
        have hk1 : Weights.kind 1 (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
            RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))))=true := by
          norm_num [Weights.kind,Weights.actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,value_bits,value]
        rw [hk0,hk1]
        simp only [Bool.false_eq_true,ite_false,ite_true,old_pair,decide_eq_true_eq]
        by_cases h : RationalSampling.chosenId δ S Δ s w<n
        · rw [ite_eq_left h,dite_eq_left h,remove_pair δ D F S Δ P κ m M E J s w h]
        · rw [ite_eq_right h,dite_eq_right h];rfl
      · have hk0 : Weights.kind 0 (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
            RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=false := by
          norm_num [Weights.kind,Weights.actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,value_bits,value]
        have hk1 : Weights.kind 1 (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
            RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=false := by
          norm_num [Weights.kind,Weights.actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,value_bits,value]
        rw [hk0,hk1]
        simp only [Bool.false_eq_true,ite_false,radius_pair,optionRadius_eq_nil]
        cases hr : RationalSampling.menuRadius δ D P κ m M E J s w e with
        | none=>simp only [ite_true,Weights.state_none]
        | some R=>
          simp only [reduceCtorEq,ite_false,ball_pair δ D F S Δ P κ m M E J s w e R hr,finset_eq_nil]
          by_cases hb : (F.filter (fun v=>δ w.val v≤R)).Nonempty
          · rw [ite_eq_right (not_not.mpr hb),ite_eq_left hb,add_pair δ D F S Δ P κ m M E J s w e R hr]
          · simp only [hb,not_false_eq_true,ite_true,ite_false,Weights.state_none]
    · rw [ite_eq_right htot,ite_eq_right htot];rfl
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
