import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.RealizedKernel

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Weights
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def stateInput (x : List Bool) : List Bool := pairBits (extractPrefix x,head (discardPrefix x))
noncomputable def stateInput_computes : PolyComputes stateInput :=
  extractPrefix_computes.pair (discardPrefix_computes.comp WordList.head_computes)
lemma stateInput_some (cfg : List Bool) (s : RationalSampling.State n) :
    stateInput (pairBits (cfg,BinarySamplingState.optionBits (some s)))=pairBits (cfg,BinarySamplingState.encode s) := by
  simp only [stateInput,BinarySamplingState.optionBits,Option.toList_some,List.map_cons,List.map_nil,
    extractPrefix_pairBits,discardPrefix_pairBits,encode,head_cons]
noncomputable def context (x : List Bool) : List Bool := encode [oracle (stateInput x),
  BinaryRational.encode (BinarySamplingOracle.total (oracle (stateInput x))),c 9 x,discardPrefix x]
noncomputable def context_computes : PolyComputes context :=
  cons_computes (stateInput_computes.comp oracle_computes)
    (cons_computes ((stateInput_computes.comp oracle_computes).comp BinarySamplingOracle.total_computes)
      (cons_computes (c_computes 9) (cons_computes discardPrefix_computes (const_computes []))))
noncomputable def actionField (i : ℕ) (x : List Bool) : List Bool := field i (discardPrefix x)
noncomputable def actionField_computes (i : ℕ) : PolyComputes (actionField i) := discardPrefix_computes.comp (field_computes i)
noncomputable def kind (k : ℕ) (x : List Bool) : Bool := decide (value (actionField 0 x)=k)
noncomputable def kind_computes (k : ℕ) : PolyComputes (fun x=>[kind k x]) := by
  simpa only [kind,value_bits] using NatOps.eq (actionField_computes 0) (const_computes k.bits)
noncomputable def active (x : List Bool) : Bool :=
  !(decide (c 3 x=[])) && decide (0<BinaryRational.decode (c 1 x))
noncomputable def active_computes : PolyComputes (fun x=>[active x]) :=
  (((c_computes 3).comp isEmpty_computes).not).and (RatOps.lt (RatOps.const 0) (RatOps.ofWords (c_computes 1)))
noncomputable def base (x : List Bool) : ℚ :=
  BinarySamplingOracle.weight (pairBits (c 0 x,actionField 1 x))/(2*BinaryRational.decode (c 1 x))
noncomputable def base_computes : PolyComputes (fun x=>BinaryRational.encode (base x)) :=
  RatOps.div (((c_computes 0).pair (actionField_computes 1)).comp BinarySamplingOracle.weight_computes)
    (RatOps.mul (RatOps.const 2) (RatOps.ofWords (c_computes 1)))
noncomputable def weight (x : List Bool) : ℚ :=
  if active x then if kind 0 x then 0 else if kind 1 x then base x
    else base x*BinaryMenu.weight (pairBits (c 2 x,actionField 2 x))
  else if kind 0 x then 1 else 0
noncomputable def weight_computes : PolyComputes (fun x=>BinaryRational.encode (weight x)) := by
  have hh := active_computes.cond ((kind_computes 0).cond (RatOps.const 0)
    ((kind_computes 1).cond base_computes
      (RatOps.mul base_computes (((c_computes 2).pair (actionField_computes 2)).comp BinaryMenu.weight_computes))))
    ((kind_computes 0).cond (RatOps.const 1) (RatOps.const 0))
  convert hh using 1
  funext x
  unfold weight
  split_ifs <;> rfl
lemma state_none : BinarySamplingState.optionBits (n:=n) none=[] := rfl
lemma state_some_ne (s : RationalSampling.State n) : BinarySamplingState.optionBits (some s)≠[] := by
  simp [BinarySamplingState.optionBits,encode,WordList.cons]
lemma weight_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (RationalSampling.State n)) (a : Sampling.Action D M E J) :
    weight (pairBits (context (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits s)),RationalSampling.actionCode D M E J a))=
      RationalSampling.transitionWeight δ D S Δ M E J s a := by
  cases s with
  | none=>
    rcases a with u | (w | ⟨w,e⟩) <;>
      simp only [context,weight,active,c,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,
        Option.getD_some,discardPrefix_pairBits,state_none,decide_true,
        Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false,kind,actionField,RationalSampling.actionCode,
        field_encode,value_bits,RationalSampling.transitionWeight,reduceCtorEq]
    all_goals norm_num
  | some s=>
    have hc : context (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)))=
        encode [BinarySamplingOracle.pack δ D S Δ s,BinaryRational.encode (RationalSampling.totalWeight δ D S Δ s),BinaryMenu.weights M E J,
          BinarySamplingState.optionBits (some s)] := by
      rw [context,stateInput_some,oracle_pair,BinarySamplingOracle.total_pack]
      simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,discardPrefix_pairBits]
    rw [hc]
    rcases a with u | (w | ⟨w,e⟩) <;>
      simp only [weight,active,c,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
        BinaryRational.decode_encode,state_some_ne,decide_false,
        Bool.not_false,Bool.true_and,decide_eq_true_eq,kind,actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,
        value_bits,base,BinarySamplingOracle.weight_pair,RationalSampling.transitionWeight,reduceCtorEq,RationalSampling.entry_weight]
    all_goals norm_num
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Client
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySamplingOracle.row BinaryIndexMap.run
variable {n : ℕ}
noncomputable def row (x : List Bool) : List Bool := BinarySamplingOracle.row (pairBits (oracle (extractPrefix x),discardPrefix x))
noncomputable def row_computes : PolyComputes row := ((extractPrefix_computes.comp oracle_computes).pair discardPrefix_computes).comp BinarySamplingOracle.row_computes
noncomputable def distances (x : List Bool) : List Bool := BinaryIndexMap.run (pairBits (row x,c 2 (extractPrefix x)))
noncomputable def distances_computes : PolyComputes distances := (row_computes.pair (extractPrefix_computes.comp (c_computes 2))).comp BinaryIndexMap.run_computes
noncomputable def population (x : List Bool) : List Bool := BinaryPopulation.run (encode [c 6 (extractPrefix x),c 8 (extractPrefix x),distances x])
noncomputable def population_computes : PolyComputes population :=
  (cons_computes (extractPrefix_computes.comp (c_computes 6)) (cons_computes (extractPrefix_computes.comp (c_computes 8))
    (cons_computes distances_computes (const_computes [])))).comp BinaryPopulation.run_computes
noncomputable def near (x : List Bool) : List Bool := BinaryNearestLeaf.run (pairBits (row x,leaves (extractPrefix x)))
noncomputable def near_computes : PolyComputes near := (row_computes.pair (extractPrefix_computes.comp leaves_computes)).comp BinaryNearestLeaf.run_computes
noncomputable def radii (x : List Bool) : List Bool := encode [c 7 (extractPrefix x),population x,near x]
noncomputable def radii_computes : PolyComputes radii := cons_computes (extractPrefix_computes.comp (c_computes 7))
  (cons_computes population_computes (cons_computes near_computes (const_computes [])))
lemma row_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : Fin n) :
    row (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s),w.val.bits))=RationalMatrix.rowEncode (δ w) := by
  rw [row,extractPrefix_pairBits,discardPrefix_pairBits,oracle_pair,BinarySamplingOracle.row_pair]
lemma distances_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : Fin n) :
    distances (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s),w.val.bits))=
      RationalArray.encode (BinaryPopulation.distanceList δ D w) := by
  rw [distances,row_pair]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinaryFinSet.encode_eq,RationalMatrix.rowEncode_eq,BinaryIndexMap.run_pack,BinaryPopulation.distanceList,RationalArray.encode]
lemma population_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : Fin n) :
    population (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s),w.val.bits))=
      BinaryRational.encode (BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w)) := by
  rw [population,distances_pair]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  exact BinaryPopulation.run_pack _ _ _
lemma near_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : Fin n) :
    near (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s),w.val.bits))=
      BinaryMenu.optBits (RationalSampling.nearestLeaf δ s w) := by
  rw [near,row_pair]
  simp only [leaves,extractPrefix_pairBits,discardPrefix_pairBits,BinarySamplingState.encode]
  exact BinaryNearestLeaf.run_pair _ _
lemma radii_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : Fin n) :
    radii (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s),w.val.bits))=
      BinaryMenu.radii κ (BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w)) (RationalSampling.nearestLeaf δ s w) := by
  rw [radii,population_pair,near_pair]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryMenu.radii]
end MetricKMedianRecovery.BitMachine.BinarySampler.Client

end OAI
