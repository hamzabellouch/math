import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.CappedFold
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelRange
import OAI.Combinatorics.KMedianRecovery.Recovery.FinImages
import OAI.Combinatorics.KMedianRecovery.Sampling.SeedTensor

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryColorLabel
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] WordList.mapWith
noncomputable def colorWord (x : List Bool) : List Bool :=
  if value x<2 then (0:ℕ).bits else if value x=2 then (1:ℕ).bits else (2:ℕ).bits
noncomputable def colorWord_computes : PolyComputes colorWord := by
  unfold colorWord
  simpa only [decide_eq_true_eq,id_eq,value_bits] using
    (NatOps.lt id_computes (const_computes (2:ℕ).bits)).cond (const_computes (0:ℕ).bits)
      ((NatOps.eq id_computes (const_computes (2:ℕ).bits)).cond (const_computes (1:ℕ).bits) (const_computes (2:ℕ).bits))
lemma colorWord_bits (i : Fin 4) : colorWord i.val.bits=(ColorLabel.color i).val.bits := by
  unfold colorWord ColorLabel.color
  simp only [value_bits]
  split_ifs <;> rfl
noncomputable def colors (x : List Bool) : List Bool :=
  mapWith (colorWord ∘ discardPrefix) (pairBits ([],BinarySeed.nest 1 x))
noncomputable def colors_computes : PolyComputes colors :=
  ((const_computes []).pair (BinarySeed.nest_computes 1)).comp
    (mapWith_computes (discardPrefix_computes.comp colorWord_computes))
lemma colors_tensor {n : ℕ} (s : Fin n→Fin 2→Bool) :
    colors (pairBits (BinarySeed.shape [n,2],BinarySeed.raw (ds:=[n]) s))=
      BinaryFinSet.table (fun i=>ColorLabel.color (Categorical.uniformBits 2 (s i))) := by
  rw [colors]
  have ht := BinarySeed.nest_tensor (ds:=[n]) (b:=2) s
  change BinarySeed.nest 1 (pairBits (BinarySeed.shape [n,2],BinarySeed.raw (ds:=[n]) s))=_ at ht
  rw [ht]
  change mapWith _ (pairBits ([],encode (List.ofFn _)))=_
  rw [mapWith_ofFn]
  unfold BinaryFinSet.table
  apply congrArg encode
  apply congrArg List.ofFn
  funext i
  simpa only [Function.comp_apply,discardPrefix_pairBits,BinarySeed.parsed] using colorWord_bits (Categorical.uniformBits 2 (s i))
noncomputable def labelOp (x : List Bool) : List Bool := (value (discardPrefix x)%value (extractPrefix x)).bits
noncomputable def labelOp_computes : PolyComputes labelOp := NatOps.mod discardPrefix_computes extractPrefix_computes
noncomputable def labels (x : List Bool) : List Bool :=
  mapWith labelOp (pairBits (extractPrefix x,BinarySeed.nest 1 (discardPrefix x)))
noncomputable def labels_computes : PolyComputes labels :=
  (extractPrefix_computes.pair (discardPrefix_computes.comp (BinarySeed.nest_computes 1))).comp (mapWith_computes labelOp_computes)
lemma labels_tensor {n : ℕ} (b : ℕ) (hb : 0<b) (s : Fin n→Fin (Nat.clog 2 b)→Bool) :
    labels (pairBits (b.bits,pairBits (BinarySeed.shape [n,Nat.clog 2 b],BinarySeed.raw (ds:=[n]) s)))=
      BinaryFinSet.table (fun i=>ColorLabel.label b hb (Categorical.uniformBits (Nat.clog 2 b) (s i))) := by
  rw [labels,extractPrefix_pairBits,discardPrefix_pairBits]
  have ht := BinarySeed.nest_tensor (ds:=[n]) (b:=Nat.clog 2 b) s
  change BinarySeed.nest 1 (pairBits (BinarySeed.shape [n,Nat.clog 2 b],BinarySeed.raw (ds:=[n]) s))=_ at ht
  rw [ht]
  change mapWith _ (pairBits (b.bits,encode (List.ofFn _)))=_
  rw [mapWith_ofFn]
  simp only [labelOp,discardPrefix_pairBits,extractPrefix_pairBits,value_bits,BinaryFinSet.table,ColorLabel.label,BinarySeed.parsed]
end MetricKMedianRecovery.BitMachine.BinaryColorLabel

namespace MetricKMedianRecovery.BitMachine.BinaryRationalPower
open WordOperations WordList RationalHeight
noncomputable def op (x : List Bool) : List Bool := BinaryRational.encode
  (BinaryRational.decode (extractPrefix x)*BinaryRational.decode (discardPrefix (discardPrefix x)))
noncomputable def op_computes : PolyComputes op := RatOps.mul (RatOps.ofWords extractPrefix_computes)
  (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes))
lemma op_pack (q a : ℚ) (w : List Bool) :
    op (pairBits (BinaryRational.encode q,pairBits (w,BinaryRational.encode a)))=BinaryRational.encode (q*a) := by
  simp only [op,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]
noncomputable def capPoly : Polynomial ℕ := 20*(Polynomial.X+1)^2
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose _
def pack (q : ℚ) (n : ℕ) : List Bool := pairBits (List.replicate n true,BinaryRational.encode q)
noncomputable def items (x : List Bool) : List Bool := repeatWords (pairBits (extractPrefix x,[]))
noncomputable def items_computes : PolyComputes items := (extractPrefix_computes.pair (const_computes [])).comp repeatWords_computes
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (cap.word x,Fold.pack (items x) (discardPrefix x) (BinaryRational.encode 1))
noncomputable def prepared_computes : PolyComputes prepared := cap.computes.pair
  (Fold.pack_computes items_computes discardPrefix_computes (const_computes (BinaryRational.encode 1)))
noncomputable def run (x : List Bool) : List Bool := CappedFold.run op (prepared x)
noncomputable def run_computes : PolyComputes run := prepared_computes.comp (CappedFold.run_computes op_computes)
lemma fold_mul (q a : ℚ) (xs : List Unit) : xs.foldl (fun r _=>q*r) a=q^xs.length*a := by
  induction xs generalizing a with
  | nil=>simp
  | cons x xs ih=>rw [List.foldl_cons,ih,List.length_cons,pow_succ];ring
lemma run_pack (q : ℚ) (n : ℕ) : run (pack q n)=BinaryRational.encode (q^n) := by
  have hi : items (pack q n)=encode ((List.replicate n ()).map (fun _=>[])) := by
    simp only [items,pack,extractPrefix_pairBits,repeatWords_pair,List.length_replicate,List.map_replicate]
  have hd : discardPrefix (pack q n)=BinaryRational.encode q := discardPrefix_pairBits _ _
  unfold run prepared
  rw [hi,hd,CappedFold.run_typed BinaryRational.encode (fun _ : Unit=>[]) (fun a _=>q*a) op
    (BinaryRational.encode q) (cap.word (pack q n)) (fun a _=>op_pack q a [])]
  · simp only [fold_mul,List.length_replicate,mul_one]
  · intro j
    rw [fold_mul,mul_one,cap.word_length]
    have hn : (List.replicate n () |>.take j).length≤n := by simp
    have he := BinaryRational.encode_height ((BinaryRational.input_height q).pow (List.take j (List.replicate n ())).length)
    apply he.trans
    have hq : (BinaryRational.encode q).length≤(pack q n).length := by simp only [pack,pairBits_length,List.length_replicate];omega
    have hN : n≤(pack q n).length := by simp only [pack,pairBits_length,List.length_replicate];omega
    have hm := Nat.mul_le_mul (hn.trans hN) hq
    simp only [capPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith
end MetricKMedianRecovery.BitMachine.BinaryRationalPower

namespace MetricKMedianRecovery.BitMachine.BinaryRationalMinKey
open WordOperations WordList
open BinaryRationalSort (entryBits)
noncomputable def run (x : List Bool) : List Bool := head (BinaryRationalSort.sort x)
noncomputable def run_computes : PolyComputes run := BinaryRationalSort.sort_computes.comp WordList.head_computes
lemma head_encode {A : Type*} (enc : A→List Bool) (xs : List A) (h : xs≠[]) :
    head (encode (xs.map enc))=enc (xs.head h) := by
  cases xs with
  | nil=>exact False.elim (h rfl)
  | cons a xs=>simp only [List.map_cons,encode,head_cons,List.head_cons]
lemma run_pack (xs : List (ℚ ×ₗ ℕ)) (h : xs.toFinset.Nonempty) :
    run (encode (xs.map entryBits))=entryBits (xs.toFinset.min' h) := by
  rw [run,BinaryRationalSort.sort_pack]
  have hn : xs.toFinset.sort (·≤·)≠[] := by
    intro he
    have hl := Finset.length_sort (s:=xs.toFinset) (·≤·)
    rw [he,List.length_nil] at hl
    exact (Finset.card_pos.mpr h).ne' hl.symm
  rw [head_encode _ _ hn,Finset.min'_eq_sorted_zero]
  simp only [List.head_eq_getElem]
end MetricKMedianRecovery.BitMachine.BinaryRationalMinKey

end OAI
