import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.NormalizeInput
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralAll

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalCall
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
namespace A
noncomputable abbrev run := BinaryIntegralAll.run
abbrev pack := @BinaryIntegralDispatch.pack
noncomputable abbrev budget := BinaryIntegralDispatch.budget
end A
def pack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) : List Bool :=
  encode [I.bits,BinaryRational.encode M,raw]
noncomputable def normInput (x : List Bool) : List Bool := pairBits (field 0 x,field 1 x)
noncomputable def normInput_computes : PolyComputes normInput := (field_computes 0).pair (field_computes 1)
noncomputable def norm : List Bool→List Bool := BinaryNormalizeInput.run ∘ normInput
noncomputable def norm_computes : PolyComputes norm := normInput_computes.comp BinaryNormalizeInput.run_computes
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ norm
noncomputable def src_computes (j : ℕ) : PolyComputes (src j) := norm_computes.comp (field_computes j)
noncomputable def fcount : List Bool→List Bool := UnaryResources.lengthBits ∘ Count.run ∘ src 3
noncomputable def fcount_computes : PolyComputes fcount := ((src_computes 3).comp Count.run_computes).comp UnaryResources.lengthBits_computes
noncomputable def clamp (x : List Bool) : List Bool := (min (value (src 4 x)) (value (fcount x))).bits
noncomputable def clamp_computes : PolyComputes clamp := NatOps.min (src_computes 4) fcount_computes
noncomputable def base (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 6 x,clamp x,field 0 x,[]]
noncomputable def base_computes : PolyComputes base := by
  unfold base
  simpa only [List.map_cons,List.map_nil] using list_computes
    [src 0,src 1,src 2,src 3,src 6,clamp,field 0,fun _=>[]] (by
      intro candidate member;refine Classical.choice ?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨src_computes 0⟩
      · exact ⟨src_computes 1⟩
      · exact ⟨src_computes 2⟩
      · exact ⟨src_computes 3⟩
      · exact ⟨src_computes 6⟩
      · exact ⟨clamp_computes⟩
      · exact ⟨field_computes 0⟩
      · exact ⟨const_computes []⟩)
noncomputable def counter (Q : Polynomial ℕ) : PolynomialCounter (A.budget Q) := PolynomialCounter.choose _
noncomputable def demand (Q : Polynomial ℕ) : List Bool→List Bool := (counter Q).word ∘ base
noncomputable def demand_computes (Q : Polynomial ℕ) : PolyComputes (demand Q) := base_computes.comp (counter Q).computes
attribute [local irreducible] counter demand base RawTake.run UnaryResources.lengthBits
noncomputable def cut (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  RawTake.run (pairBits (UnaryResources.lengthBits (demand Q x),field 2 x))
noncomputable def cut_computes (Q : Polynomial ℕ) : PolyComputes (cut Q) :=
  (((demand_computes Q).comp UnaryResources.lengthBits_computes).pair (field_computes 2)).comp RawTake.run_computes
noncomputable def ready (Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 6 x,clamp x,field 0 x,cut Q x]
noncomputable def ready_computes (Q : Polynomial ℕ) : PolyComputes (ready Q) := by
  unfold ready
  simpa only [List.map_cons,List.map_nil] using list_computes
    [src 0,src 1,src 2,src 3,src 6,clamp,field 0,cut Q] (by
      intro candidate member;refine Classical.choice ?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨src_computes 0⟩
      · exact ⟨src_computes 1⟩
      · exact ⟨src_computes 2⟩
      · exact ⟨src_computes 3⟩
      · exact ⟨src_computes 6⟩
      · exact ⟨clamp_computes⟩
      · exact ⟨field_computes 0⟩
      · exact ⟨cut_computes Q⟩)
noncomputable def call (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool := A.run v C Q d ∘ ready Q
noncomputable def call_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (call v C Q d) :=
  (ready_computes Q).comp (BinaryIntegralAll.run_computes v C Q d)
attribute [local irreducible] call BinaryIntegralAll.run BinaryIntegralDispatch.budget ready norm src clamp BinaryInputParser.Metric.count
noncomputable def projectInput (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (x : List Bool) : List Bool :=
  pairBits (BinaryInputParser.Metric.count (field 0 x),call v C Q d x)
noncomputable def projectInput_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (projectInput v C Q d) :=
  ((field_computes 0).comp BinaryInputParser.Metric.count_computes).pair (call_computes v C Q d)
noncomputable def run (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : List Bool→List Bool :=
  BinaryTaggedSets.unshift ∘ projectInput v C Q d
noncomputable def run_computes (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) : PolyComputes (run v C Q d) :=
  (projectInput_computes v C Q d).comp BinaryTaggedSets.unshift_computes
noncomputable abbrev matrix (I : RationalMetricInput) (M : ℚ) :=
  BinaryRoundingMatrix.round (BinaryDuplicateMatrix.duplicate I.distance)
    ((IntegralAssembly.gammaRat/16)*M/I.clients.card) (Rounding.cap I.clients.card (IntegralAssembly.gamma/16))
noncomputable abbrev integralPack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :=
  A.pack (matrix I M) (I.clients.image BinaryTaggedSets.left) (I.facilities.image BinaryTaggedSets.right)
    (Rounding.cap I.clients.card (IntegralAssembly.gamma/16)) (min I.budget I.facilities.card) I.bits raw
lemma norm_pack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    norm (pack I M raw)=BinaryNormalizeInput.run (pairBits (I.bits,BinaryRational.encode M)) := by
  simp only [norm,normInput,pack,Function.comp_apply,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma right_card (I : RationalMetricInput) : (I.facilities.image BinaryTaggedSets.right).card=I.facilities.card := by
  apply Finset.card_image_of_injective
  intro a b h
  have hh:=congrArg Fin.val h
  simp only [BinaryTaggedSets.right,Fin.val_natAdd] at hh
  exact Fin.ext (by omega)
lemma clamp_pack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    clamp (pack I M raw)=(min I.budget I.facilities.card).bits := by
  simp only [clamp,fcount,src,Function.comp_apply,norm_pack,BinaryNormalizeInput.run_bits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.encode_eq,Count.run_encode,
    List.length_map,Finset.length_sort,UnaryResources.lengthBits_eq,List.length_replicate,value_bits,right_card]
lemma base_pack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) : base (pack I M raw)=integralPack I M [] := by
  rw [base,clamp_pack]
  simp only [src,Function.comp_apply,norm_pack]
  simp only [BinaryNormalizeInput.run_bits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,integralPack,A.pack,BinaryIntegralDispatch.pack,matrix]
lemma demand_length (Q : Polynomial ℕ) (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    (demand Q (pack I M raw)).length=(A.budget Q).eval (integralPack I M []).length := by
  rw [demand,Function.comp_apply,(counter Q).word_length,base_pack]
lemma cut_pack (Q : Polynomial ℕ) (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    cut Q (pack I M raw)=raw.take ((A.budget Q).eval (integralPack I M []).length) := by
  rw [cut,UnaryResources.lengthBits_eq,demand_length]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,RawTake.run_pack]
lemma ready_pack (Q : Polynomial ℕ) (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    ready Q (pack I M raw)=integralPack I M (raw.take ((A.budget Q).eval (integralPack I M []).length)) := by
  rw [ready,clamp_pack,cut_pack]
  simp only [src,Function.comp_apply,norm_pack]
  simp only [BinaryNormalizeInput.run_bits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,integralPack,A.pack,BinaryIntegralDispatch.pack,matrix]
lemma run_pack (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    run v C Q d (pack I M raw)=BinaryTaggedSets.unshift (pairBits (I.pointCount.bits,
      A.run v C Q d (integralPack I M (raw.take ((A.budget Q).eval (integralPack I M []).length))))) := by
  rw [run,Function.comp_apply,projectInput,call,Function.comp_apply,ready_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,Option.getD_some,BinaryInputParser.Metric.count_bits]
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList
open BinaryRationalSort (entryBits)
variable {n : ℕ}
def keys (F : Finset (Fin n)) (row : Fin n→ℚ) : Finset (ℚ ×ₗ ℕ) :=
  F.image (fun f=>toLex (row f,f.val))
lemma keys_nonempty (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) :
    (keys F row).Nonempty := hF.image _
noncomputable def key (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) : ℚ ×ₗ ℕ :=
  (keys F row).min' (keys_nonempty F hF row)
lemma key_mem (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) :
    ∃ f∈F,toLex (row f,f.val)=key F hF row :=
  Finset.mem_image.mp (Finset.min'_mem _ _)
lemma key_lt (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) :
    (ofLex (key F hF row)).2<n := by
  obtain ⟨f,_,he⟩:=key_mem F hF row
  rw [←he]
  exact f.isLt
noncomputable def pick (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) : Fin n :=
  ⟨(ofLex (key F hF row)).2,key_lt F hF row⟩
lemma pick_mem (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) : pick F hF row∈F := by
  obtain ⟨f,hf,he⟩:=key_mem F hF row
  have hp : pick F hF row=f := by apply Fin.ext;exact (congrArg (fun z:ℚ ×ₗ ℕ=>(ofLex z).2) he).symm
  exact hp.symm ▸ hf
lemma pick_key (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) :
    toLex (row (pick F hF row),(pick F hF row).val)=key F hF row := by
  obtain ⟨f,hf,he⟩:=key_mem F hF row
  have hp : pick F hF row=f := by apply Fin.ext;exact (congrArg (fun z:ℚ ×ₗ ℕ=>(ofLex z).2) he).symm
  rw [hp];exact he
lemma pick_min (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) (f : Fin n) (hf : f∈F) :
    row (pick F hF row)≤row f := by
  have hh:=Finset.min'_le (keys F row) (toLex (row f,f.val)) (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
  change key F hF row≤toLex (row f,f.val) at hh
  rw [←pick_key F hF row] at hh
  exact Prod.Lex.monotone_fst _ _ hh
noncomputable def rowRun (x : List Bool) : List Bool :=
  discardPrefix (BinaryRationalMinKey.run (mapWith BinarySamplingReference.original x))
noncomputable def rowRun_computes : PolyComputes rowRun :=
  ((mapWith_computes BinarySamplingReference.original_computes).comp BinaryRationalMinKey.run_computes).comp discardPrefix_computes
lemma rowRun_pack (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) :
    rowRun (pairBits (RationalMatrix.rowEncode row,BinaryFinSet.encode F))=(pick F hF row).val.bits := by
  rw [rowRun,BinaryFinSet.encode_eq,mapWith_encode]
  simp only [List.map_map,Function.comp_def,BinarySamplingReference.original_pack]
  have he : ((F.sort (·≤·)).map (fun f=>toLex (row f,f.val))).toFinset=keys F row := by
    ext x
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,keys,Finset.mem_image]
  have hne : ((F.sort (·≤·)).map (fun f=>toLex (row f,f.val))).toFinset.Nonempty := by rw [he];exact keys_nonempty F hF row
  have hh:=BinaryRationalMinKey.run_pack ((F.sort (·≤·)).map (fun f=>toLex (row f,f.val))) hne
  simp only [List.map_map,Function.comp_def] at hh
  rw [hh]
  simp only [entryBits,discardPrefix_pairBits]
  have hm : (((F.sort (·≤·)).map (fun f=>toLex (row f,f.val))).toFinset.min' hne)=key F hF row := by
    simp only [key,he]
  rw [hm]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
