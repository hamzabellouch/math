import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerWeights

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField actionField_computes)
attribute [local irreducible] BinaryMenu.radius WordList.filterWith Client.row
variable {n : ℕ}
noncomputable def input (x : List Bool) : List Bool := Weights.stateInput (extractPrefix x)
noncomputable def input_computes : PolyComputes input := extractPrefix_computes.comp Weights.stateInput_computes
noncomputable def clientInput (x : List Bool) : List Bool := pairBits (input x,actionField 1 x)
noncomputable def clientInput_computes : PolyComputes clientInput := input_computes.pair (actionField_computes 1)
noncomputable def chosen (x : List Bool) : List Bool := discardPrefix
  (BinarySamplingOracle.reference (pairBits (oracle (input x),actionField 1 x)))
noncomputable def chosen_computes : PolyComputes chosen :=
  ((((input_computes.comp oracle_computes).pair (actionField_computes 1)).comp BinarySamplingOracle.reference_computes).comp discardPrefix_computes)
noncomputable def radius (x : List Bool) : List Bool := BinaryMenu.radius (pairBits (Client.radii (clientInput x),actionField 2 x))
noncomputable def radius_computes : PolyComputes radius :=
  ((clientInput_computes.comp Client.radii_computes).pair (actionField_computes 2)).comp BinaryMenu.radius_computes
noncomputable def within (x : List Bool) : Bool := decide
  (BinaryRational.decode (Lookup.run (pairBits (discardPrefix x,extractPrefix (extractPrefix x))))≤
    BinaryRational.decode (discardPrefix (extractPrefix x)))
noncomputable def within_computes : PolyComputes (fun x=>[within x]) :=
  RatOps.le (RatOps.ofWords ((discardPrefix_computes.pair (extractPrefix_computes.comp extractPrefix_computes)).comp Lookup.run_computes))
    (RatOps.ofWords (extractPrefix_computes.comp discardPrefix_computes))
noncomputable def ball (x : List Bool) : List Bool := filterWith within (pairBits
  (pairBits (Client.row (clientInput x),head (radius x)),c 3 (input x)))
noncomputable def ball_computes : PolyComputes ball :=
  (((clientInput_computes.comp Client.row_computes).pair (radius_computes.comp WordList.head_computes)).pair
    (input_computes.comp (c_computes 3))).comp (filterWith_computes within_computes)
lemma chosen_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n)
    (w : D) (e : Option (Sampling.Entry M E J)) :
    chosen (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (e.elim (Sum.inr (Sum.inl w)) (fun e=>Sum.inr (Sum.inr (w,e))))))=
      (RationalSampling.chosenId δ S Δ s w).bits := by
  cases e <;> simp only [Option.elim,chosen,input,extractPrefix_pairBits,Weights.stateInput_some,oracle_pair,actionField,
    RationalSampling.actionCode,discardPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingOracle.reference_pair]
lemma radius_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n)
    (w : D) (e : Sampling.Entry M E J) :
    radius (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=
      BinaryMenu.optBits (RationalSampling.menuRadius δ D P κ m M E J s w e) := by
  simp only [radius,clientInput,input,extractPrefix_pairBits,Weights.stateInput_some,actionField,RationalSampling.actionCode,
    discardPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Client.radii_pair]
  rcases e with i | (i | i) <;>
    norm_num [RationalSampling.entryCode,BinaryMenu.radius_pair,RationalSampling.menuRadius]
lemma within_pair (δ : Fin n→Fin n→ℚ) (w v : Fin n) (R : ℚ) :
    within (pairBits (pairBits (RationalMatrix.rowEncode (δ w),BinaryRational.encode R),v.val.bits))=decide (δ w v≤R) := by
  simp only [within,extractPrefix_pairBits,discardPrefix_pairBits,RationalMatrix.rowEncode_eq,lookup_ofFn,BinaryRational.decode_encode]
lemma ball_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n)
    (w : D) (e : Sampling.Entry M E J) (R : ℚ) (hr : RationalSampling.menuRadius δ D P κ m M E J s w e=some R) :
    ball (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=
      BinaryFinSet.encode (F.filter (fun v=>δ w.val v≤R)) := by
  rw [ball,radius_pair,hr]
  simp only [clientInput,input,extractPrefix_pairBits,Weights.stateInput_some,actionField,RationalSampling.actionCode,
    discardPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Client.row_pair,
    BinaryMenu.optBits,Option.toList_some,List.map_cons,List.map_nil]
  simp only [WordList.encode,WordList.head_cons]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinaryFinSet.encode_eq,filterWith_encode,List.filter_map,Function.comp_def,within_pair]
  congr 1
  congr 1
  symm
  have hn := (Finset.sort_nodup F (·≤·)).filter (fun v=>decide (δ w.val v≤R))
  have hp := (Finset.pairwise_sort F (·≤·)).filter (fun v=>decide (δ w.val v≤R))
  have hh := (List.toFinset_sort (r:=(·≤·)) hn).mpr hp
  simpa only [List.toFinset_filter,Finset.sort_toFinset,decide_eq_true_eq] using hh
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
