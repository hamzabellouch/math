import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchBalls
import OAI.Combinatorics.KMedianRecovery.Sampling.MetricBestProbability
import OAI.Combinatorics.KMedianRecovery.Encoding.FinSetDecode

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def keep (x : List Bool) : Bool :=
  BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def keep_computes : PolyComputes (fun x=>[keep x]) :=
  (discardPrefix_computes.pair extractPrefix_computes).comp BinaryNatSet.contains_computes
noncomputable def clip (x : List Bool) : List Bool :=
  filterWith keep (pairBits (field 3 x,field 0 x))
noncomputable def clip_computes : PolyComputes clip :=
  ((field_computes 3).pair (field_computes 0)).comp (filterWith_computes keep_computes)
noncomputable def size : List Bool→List Bool := UnaryResources.lengthBits ∘ Count.run ∘ clip
noncomputable def size_computes : PolyComputes size := (clip_computes.comp Count.run_computes).comp UnaryResources.lengthBits_computes
noncomputable def run (x : List Bool) : List Bool :=
  if 0<value (size x) then
    if value (size x)≤value (field 2 x) then clip x else field 1 x
  else field 1 x
noncomputable def run_computes : PolyComputes run := by
  have hp:=NatOps.lt (const_computes (0:ℕ).bits) size_computes
  have hk:=NatOps.le size_computes (field_computes 2)
  unfold run
  simpa only [value_bits,decide_eq_true_eq] using
    hp.cond (hk.cond clip_computes (field_computes 1)) (field_computes 1)
variable {n : ℕ}
def pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) : List Bool :=
  encode [BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits,raw]
noncomputable def clipped (F : Finset (Fin n)) (raw : List Bool) : Finset (Fin n) :=
  F.filter (fun i=>BinaryNatSet.contains (pairBits (i.val.bits,raw)))
noncomputable def output (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) : Finset (Fin n) :=
  if (clipped F raw).Nonempty ∧ (clipped F raw).card≤k then clipped F raw else S
lemma clip_pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) :
    clip (pack F S k raw)=BinaryFinSet.encode (clipped F raw) := by
  simp only [clip,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.encode_eq,filterWith_encode,List.filter_map,Function.comp_def,keep,
    extractPrefix_pairBits,discardPrefix_pairBits,clipped]
  congr 2
  simpa only [Bool.decide_coe] using BinaryFinSet.filter_sort F (fun i=>BinaryNatSet.contains (pairBits (i.val.bits,raw))=true)
lemma size_pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) :
    size (pack F S k raw)=(clipped F raw).card.bits := by
  simp only [size,Function.comp_apply,clip_pack,BinaryFinSet.encode_eq,Count.run_encode,List.length_map,Finset.length_sort,
    UnaryResources.lengthBits_eq,List.length_replicate]
lemma run_pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) :
    run (pack F S k raw)=BinaryFinSet.encode (output F S k raw) := by
  rw [run,size_pack,clip_pack]
  simp only [value_bits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,output,Finset.card_pos]
  split_ifs <;> simp_all
lemma output_feasible (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    output F S k raw⊆F ∧ (output F S k raw).Nonempty ∧ (output F S k raw).card≤k := by
  unfold output
  split_ifs with h
  · exact ⟨Finset.filter_subset _ _,h⟩
  · exact ⟨hSF,hS,hSk⟩
lemma clipped_encode (F U : Finset (Fin n)) :
    clipped F (BinaryFinSet.encode U)=F∩U := by
  classical
  have hh:=BinaryFinSet.decode_encode U
  ext i
  have hi:=Finset.ext_iff.mp hh i
  simp only [BinaryFinSet.decode,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  simp only [clipped,Finset.mem_filter,Finset.mem_inter,hi]
lemma output_encode (F S U : Finset (Fin n)) (k : ℕ) (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤k) :
    output F S k (BinaryFinSet.encode U)=U := by
  rw [output,clipped_encode,Finset.inter_eq_right.mpr hUF,ite_eq_left ⟨hU,hUk⟩]
lemma run_encode (F S U : Finset (Fin n)) (k : ℕ) (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤k) :
    run (pack F S k (BinaryFinSet.encode U))=BinaryFinSet.encode U := by
  rw [run_pack,output_encode F S U k hUF hU hUk]
end MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def metricContext (x : List Bool) : List Bool := encode [field 0 x,field 1 x]
noncomputable def metricContext_computes : PolyComputes metricContext := cons_computes (field_computes 0)
  (cons_computes (field_computes 1) (const_computes []))
noncomputable def sanitizeContext (x : List Bool) : List Bool := encode [field 2 x,field 3 x,field 4 x]
noncomputable def sanitizeContext_computes : PolyComputes sanitizeContext := cons_computes (field_computes 2)
  (cons_computes (field_computes 3) (cons_computes (field_computes 4) (const_computes [])))
noncomputable def atRawInput (x : List Bool) : List Bool := encode [field 0 (extractPrefix x),field 1 (extractPrefix x),
  field 2 (extractPrefix x),discardPrefix x]
noncomputable def atRawInput_computes : PolyComputes atRawInput := cons_computes (extractPrefix_computes.comp (field_computes 0))
  (cons_computes (extractPrefix_computes.comp (field_computes 1)) (cons_computes (extractPrefix_computes.comp (field_computes 2))
    (cons_computes discardPrefix_computes (const_computes []))))
noncomputable def atRaw : List Bool→List Bool := BinaryCandidateSanitize.run ∘ atRawInput
noncomputable def atRaw_computes : PolyComputes atRaw := atRawInput_computes.comp BinaryCandidateSanitize.run_computes
noncomputable def candidates (x : List Bool) : List Bool := mapWith atRaw (pairBits (sanitizeContext x,field 5 x))
noncomputable def candidates_computes : PolyComputes candidates := by
  have candidatesComputes := (sanitizeContext_computes.pair (field_computes 5)).comp (mapWith_computes atRaw_computes)
  unfold candidates
  simpa only [Function.comp_def] using candidatesComputes
noncomputable def run (x : List Bool) : List Bool := BinaryMetricBest.run
  (pairBits (metricContext x,pairBits (field 3 x,candidates x)))
noncomputable def run_computes : PolyComputes run :=
  (metricContext_computes.pair ((field_computes 3).pair candidates_computes)).comp BinaryMetricBest.run_computes
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits,encode xs]
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) : Finset (Fin n) :=
  BinaryMetricBest.best δ D S (xs.map (BinaryCandidateSanitize.output F S k))
lemma atRaw_pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) :
    atRaw (pairBits (encode [BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits],raw))=
      BinaryFinSet.encode (BinaryCandidateSanitize.output F S k raw) := by
  simp only [atRaw,Function.comp_apply,atRawInput,extractPrefix_pairBits,discardPrefix_pairBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinaryCandidateSanitize.run_pack F S k raw
lemma candidates_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) :
    candidates (pack δ D F S k xs)=encode (xs.map (fun raw=>BinaryFinSet.encode (BinaryCandidateSanitize.output F S k raw))) := by
  simp only [candidates,sanitizeContext,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,mapWith_encode,atRaw_pack]
lemma run_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) :
    run (pack δ D F S k xs)=BinaryFinSet.encode (output δ D F S k xs) := by
  rw [run,candidates_pack]
  have hm : metricContext (pack δ D F S k xs)=BinaryMetricBest.context δ D := by
    simp only [metricContext,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,BinaryMetricBest.context]
  have hs : field 3 (pack δ D F S k xs)=BinaryFinSet.encode S := by simp only [pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hm,hs]
  have hh:=BinaryMetricBest.run_pack δ D S (xs.map (BinaryCandidateSanitize.output F S k))
  simpa only [BinaryRationalBest.pack,List.map_map,Function.comp_def,output] using hh
lemma output_feasible (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool))
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    output δ D F S k xs⊆F ∧ (output δ D F S k xs).Nonempty ∧ (output δ D F S k xs).card≤k := by
  apply BinaryMetricBest.best_property δ D S _ (fun U=>U⊆F ∧ U.Nonempty ∧ U.card≤k) ⟨hSF,hS,hSk⟩
  intro U hU
  obtain ⟨raw,_,rfl⟩:=List.mem_map.mp hU
  exact BinaryCandidateSanitize.output_feasible F S k raw hSF hS hSk
variable [PseudoMetricSpace (Fin n)]
lemma realCost_le_self (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool))
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    Completion.realCost D (output δ D F S k xs)≤Completion.realCost D S := by
  apply BinaryMetricBest.realCost_le_self δ hδ D S hS
  intro U hU
  obtain ⟨raw,_,rfl⟩:=List.mem_map.mp hU
  exact (BinaryCandidateSanitize.output_feasible F S k raw hSF hS hSk).2.1
lemma realCost_le_good (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool))
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) (U : Finset (Fin n))
    (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤k) (hmem : BinaryFinSet.encode U∈xs) :
    Completion.realCost D (output δ D F S k xs)≤Completion.realCost D U := by
  apply BinaryMetricBest.realCost_le_mem δ hδ D S hS _ _ U
  · exact List.mem_map.mpr ⟨BinaryFinSet.encode U,hmem,BinaryCandidateSanitize.output_encode F S U k hUF hU hUk⟩
  · intro V hV
    obtain ⟨raw,_,rfl⟩:=List.mem_map.mp hV
    exact (BinaryCandidateSanitize.output_feasible F S k raw hSF hS hSk).2.1
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
