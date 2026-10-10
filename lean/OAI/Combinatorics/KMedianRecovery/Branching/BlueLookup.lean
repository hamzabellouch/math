import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelSize
import OAI.Combinatorics.KMedianRecovery.Branching.BlueBlocksMachine
import OAI.Combinatorics.KMedianRecovery.Branching.BlueTable

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLookup
open WordOperations WordList
variable {L A : Type*} [LinearOrder L]
def encode (key : Finset L→List Bool) (enc : A→List Bool) (T : BlueDP.Table L A) : List Bool :=
  WordList.encode (T.map (fun z=>pairBits (key z.1,BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc) z.2)))
noncomputable def matchKey (x : List Bool) : Bool := WordEq.eq (pairBits (extractPrefix x,extractPrefix (discardPrefix x)))
noncomputable def matchKey_computes : PolyComputes (fun x=>[matchKey x]) :=
  (extractPrefix_computes.pair (discardPrefix_computes.comp extractPrefix_computes)).comp WordEq.eq_computes
noncomputable def run (x : List Bool) : List Bool := discardPrefix (List.tail (Find.run matchKey x))
noncomputable def run_computes : PolyComputes run := ((Find.run_computes matchKey_computes).comp WordOperations.tail_computes).comp discardPrefix_computes
lemma run_pack (key : Finset L→List Bool) (enc : A→List Bool) (hk : Function.Injective key)
    (T : BlueDP.Table L A) (U : Finset L) : run (pairBits (key U,encode key enc T))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc) (BlueDP.lookup U T) := by
  simp only [run,encode,Find.run_encode]
  induction T with
  | nil=>simp [Find.optionEncode,BlueDP.lookup,BinaryBlueChoice.encode,List.tail,discardPrefix]
  | cons z T ih=>
    rcases z with ⟨V,c⟩
    simp only [List.map_cons,List.find?_cons,matchKey,extractPrefix_pairBits,discardPrefix_pairBits,WordEq.eq_pair,
      hk.eq_iff,BlueDP.lookup]
    split_ifs with h
    · simp [h,Find.optionEncode,List.tail]
    · simp only [h,decide_false]
      simpa only [matchKey,extractPrefix_pairBits,discardPrefix_pairBits,WordEq.eq_pair] using ih
end MetricKMedianRecovery.BitMachine.BinaryBlueLookup
namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
lemma encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro S T he
  rw [encode_eq,encode_eq] at he
  have hh:=WordList.encode_injective he
  have hin : Function.Injective (fun i : Fin n=>i.val.bits) := by
    intro i j hij
    apply Fin.val_injective
    have h:=congrArg BinaryArithmetic.value hij
    simpa only [BinaryArithmetic.value_bits] using h
  have hh' := List.map_injective_iff.mpr hin hh
  simpa only [Finset.sort_toFinset] using congrArg List.toFinset hh'
end MetricKMedianRecovery.BitMachine.BinaryFinSet

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
abbrev atomEnc (er : R→List Bool) := BinaryBlueItem.atomEnc (fun i : Fin m=>i.val.bits) er (n:=n)
def ctxPack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) : List Bool :=
  encode [BinaryBlueItem.records (fun i=>i.val.bits) er B label q,BinaryFinSet.encode F,
    encode ((BlueDP.states U).map BinaryFinSet.encode),BinaryBlueLookup.encode BinaryFinSet.encode (atomEnc er) T]
noncomputable def ctx (x : List Bool) : List Bool := extractPrefix (extractPrefix x)
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def whole (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
noncomputable def whole_computes : PolyComputes whole := extractPrefix_computes.comp discardPrefix_computes
noncomputable def block (x : List Bool) : List Bool := BinaryBlueBlocks.run
  (pairBits (pairBits (field 0 (ctx x),discardPrefix x),field 1 (ctx x)))
noncomputable def block_computes : PolyComputes block :=
  (((ctx_computes.comp (field_computes 0)).pair discardPrefix_computes).pair
    (ctx_computes.comp (field_computes 1))).comp BinaryBlueBlocks.run_computes
noncomputable def old (x : List Bool) : List Bool := BinaryBlueLookup.run
  (pairBits (BinaryNatSet.diff (pairBits (whole x,discardPrefix x)),field 3 (ctx x)))
noncomputable def old_computes : PolyComputes old :=
  (((whole_computes.pair discardPrefix_computes).comp BinaryNatSet.diff_computes).pair
    (ctx_computes.comp (field_computes 3))).comp BinaryBlueLookup.run_computes
noncomputable def op (x : List Bool) : List Bool := BinaryBlueMerge.run (pairBits (block x,old x))
noncomputable def op_computes : PolyComputes op := by
  unfold op
  have computes := (block_computes.pair old_computes).comp BinaryBlueMerge.run_computes
  simpa only [Function.comp_def] using computes
lemma finValBits_injective : Function.Injective (fun i : Fin m=>i.val.bits) := by
  intro i j h
  have hh:=congrArg BinaryArithmetic.value h
  exact Fin.val_injective (by simpa only [BinaryArithmetic.value_bits] using hh)
lemma op_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U W V : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) :
    op (pairBits (pairBits (ctxPack er B F label q U T,BinaryFinSet.encode W),BinaryFinSet.encode V))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (atomEnc er))
        (BlueDP.merge (BlueDP.block B F label q V) (BlueDP.lookup (W\V) T)) := by
  simp only [op,block,old,ctx,whole,extractPrefix_pairBits,discardPrefix_pairBits,ctxPack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.diff_pack]
  rw [show BinaryFinSet.encode V=BinaryBlueBlocks.labelsEnc (fun i : Fin m=>i.val.bits) V by
    exact BinaryFinSet.encode_eq V]
  rw [BinaryBlueBlocks.run_pack _ er finValBits_injective]
  rw [BinaryBlueLookup.run_pack _ _ BinaryFinSet.encode_injective,BinaryBlueMerge.run_pack]
noncomputable def run (x : List Bool) : List Bool := BinaryBlueChoice.select
  (mapWith op (pairBits (x,BinaryBlueStates.blocks 3 x)))
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := ((id_computes.pair (BinaryBlueStates.blocks_computes 3)).comp (mapWith_computes op_computes)).comp BinaryBlueChoice.select_computes
  simpa only [Function.comp_def,id_eq] using computes
lemma subset_capacity (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U W : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) (hW : W⊆U) :
    2^W.card*(2*(BinaryFinSet.encode W).length+2)≤
      ((pairBits (ctxPack er B F label q U T,BinaryFinSet.encode W)).length+1)^3 := by
  have hu : 2^U.card≤(ctxPack er B F label q U T).length := by
    apply (show 2^U.card≤(encode ((BlueDP.states U).map BinaryFinSet.encode)).length from by
      simpa only [List.length_map,BlueDP.states_length] using length_le_encode ((BlueDP.states U).map BinaryFinSet.encode)).trans
    exact member_length (by simp)
  have hw : 2^W.card≤(ctxPack er B F label q U T).length :=
    (Nat.pow_le_pow_right (by omega) (Finset.card_le_card hW)).trans hu
  simp only [pairBits_length]
  calc
    _ ≤ (ctxPack er B F label q U T).length*(2*(BinaryFinSet.encode W).length+2) := Nat.mul_le_mul_right _ hw
    _ ≤ (2*(ctxPack er B F label q U T).length+1+(BinaryFinSet.encode W).length+1)^2 := by nlinarith
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
lemma run_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U W : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) (hW : W⊆U) :
    run (pairBits (ctxPack er B F label q U T,BinaryFinSet.encode W))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (atomEnc er))
        (BlueDP.select ((BlueDP.enumBlocks W).map (fun V=>BlueDP.merge (BlueDP.block B F label q V) (BlueDP.lookup (W\V) T)))) := by
  rw [run,BinaryBlueStates.blocks_pack 3 _ W (subset_capacity er B F label q U W T hW),mapWith_encode]
  simp only [List.map_map,Function.comp_def,op_pack]
  exact BinaryBlueChoice.select_map _ _ _
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

end OAI
