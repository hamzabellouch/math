import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RawUnary
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalResources
import OAI.Combinatorics.KMedianRecovery.Sampling.TensorEquiv
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalSize

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
def outputPack (ctx : List Bool) (part : Fin q→Fin a)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) : List Bool :=
  pairBits (runPack ctx part T (List.ofFn seed.1),seedBits seed.2)
noncomputable def output (g : List Bool→List Bool) (x : List Bool) : List Bool :=
  draw (encode [field 1 (run g (extractPrefix x)),discardPrefix x,
    UnaryResources.lengthBits (field 2 (extractPrefix x))])
noncomputable def output_computes {g : List Bool→List Bool} (hg : PolyComputes g) : PolyComputes (output g) :=
  (cons_computes ((extractPrefix_computes.comp (run_computes hg)).comp (field_computes 1))
    (cons_computes discardPrefix_computes (cons_computes
      ((extractPrefix_computes.comp (field_computes 2)).comp UnaryResources.lengthBits_computes)
      (const_computes [])))).comp draw_computes
lemma output_pack (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
    output g (outputPack ctx part seed)=encode ((drawn
      (Categorical.Selected.greedyRun part (rule part hp) (fun S=>(G S:ℝ)) seed.1).2 seed.2).map elemBits) := by
  unfold output outputPack
  rw [extractPrefix_pairBits,discardPrefix_pairBits,run_ofFn g ctx G hg part hp]
  simp only [stateBits,runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,UnaryResources.lengthBits_eq,List.length_replicate]
  simpa only [drawPack,omitted_end] using draw_pack elemBits
    (Categorical.Selected.greedyRun part (rule part hp) (fun S=>(G S:ℝ)) seed.1).2 seed.2 a
lemma output_correct (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) :
    ∃ xs : List (Fin q),output g (outputPack ctx part seed)=encode (xs.map elemBits) ∧
      xs.toFinset=Categorical.Selected.greedyOutput part (rule part hp) (fun S=>(G S:ℝ)) seed := by
  exact ⟨_,output_pack g ctx G hg part hp seed,drawn_toFinset _ _⟩
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape
open BinarySeed
variable (q a b L : ℕ)
abbrev M : ℕ := count [2^b,q,L,a] b
abbrev K : ℕ := count [a] b

def tensors : (Categorical.BinaryOracleIndex (Fin q) a b L→Bool)≃
    Tensor [2^b,q,L,a] b × Tensor [a] b where
  toFun bits := (fun t e l j i=>bits (.inl (t,e,l,j),i),fun j i=>bits (.inr j,i))
  invFun s := fun idx=>match idx.1 with
    | .inl (t,e,l,j)=>s.1 t e l j idx.2
    | .inr j=>s.2 j idx.2
  left_inv bits := by
    funext idx
    rcases idx with ⟨idx,i⟩
    rcases idx with ⟨t,e,l,j⟩ | j <;> rfl
  right_inv s := by rfl

def split : (Fin (M q a b L+K a b)→Bool)≃
    (Fin (M q a b L)→Bool)×(Fin (K a b)→Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)
def tensorPair : (Fin (M q a b L+K a b)→Bool)≃Tensor [2^b,q,L,a] b × Tensor [a] b :=
  (split q a b L).trans (Equiv.prodCongr (tensorEquiv _ b) (tensorEquiv _ b))
def layout : (Fin (M q a b L+K a b)→Bool)≃(Categorical.BinaryOracleIndex (Fin q) a b L→Bool) :=
  (tensorPair q a b L).trans (tensors q a b L).symm

def raw (bits : Categorical.BinaryOracleIndex (Fin q) a b L→Bool) : List Bool :=
  BinarySeed.raw ((tensors q a b L bits).1)++BinarySeed.raw ((tensors q a b L bits).2)
lemma tensorPair_raw (s : Fin (M q a b L+K a b)→Bool) :
    BinarySeed.raw ((tensorPair q a b L s).1)++BinarySeed.raw ((tensorPair q a b L s).2)=List.ofFn s := by
  change BinarySeed.raw (tensorEquiv _ b _ )++BinarySeed.raw (tensorEquiv _ b _)=List.ofFn s
  rw [raw_tensorEquiv,raw_tensorEquiv]
  rw [List.ofFn_add]
  rfl
lemma raw_layout (s : Fin (M q a b L+K a b)→Bool) : raw q a b L (layout q a b L s)=List.ofFn s := by
  unfold raw layout
  rw [Equiv.trans_apply,Equiv.apply_symm_apply]
  exact tensorPair_raw q a b L s
lemma raw_left_length (bits : Categorical.BinaryOracleIndex (Fin q) a b L→Bool) :
    (BinarySeed.raw ((tensors q a b L bits).1)).length=M q a b L := by
  rw [BinarySeed.raw_length,←count_eq]
lemma raw_right_length (bits : Categorical.BinaryOracleIndex (Fin q) a b L→Bool) :
    (BinarySeed.raw ((tensors q a b L bits).2)).length=K a b := by
  rw [BinarySeed.raw_length,←count_eq]
lemma parsed_left (bits : Categorical.BinaryOracleIndex (Fin q) a b L→Bool) :
    BinarySeed.parsed ((tensors q a b L bits).1)=
      WordList.encode (List.ofFn (fun t=>oracleBits ((Categorical.binarySeedEquiv (Fin q) a b L bits).1 t))) := rfl
lemma parsed_right (bits : Categorical.BinaryOracleIndex (Fin q) a b L→Bool) :
    BinarySeed.parsed ((tensors q a b L bits).2)=
      seedBits ((Categorical.binarySeedEquiv (Fin q) a b L bits).2) := rfl
lemma layout_average (X : (Categorical.BinaryOracleIndex (Fin q) a b L→Bool)→ℝ) :
    FiniteSampling.average (fun s : Fin (M q a b L+K a b)→Bool=>X (layout q a b L s))=FiniteSampling.average X :=
  FiniteSampling.average_equiv (layout q a b L) _ _ (fun _=>rfl)
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources
open WordOperations WordList BinaryArithmetic
open Categorical.Explicit

def pack (q a : ℕ) : List Bool := pairBits (List.replicate q true,List.replicate a true)
noncomputable def bword (x : List Bool) : List Bool :=
  RepeatedAppend.copies 2 (RawUnary.run (UnaryResources.inc (UnaryResources.lengthBits (discardPrefix x))))++List.replicate 10 true
noncomputable def bword_computes : PolyComputes bword :=
  ((UnaryResources.copy_computes (const_computes [true,true])
    (((discardPrefix_computes.comp UnaryResources.lengthBits_computes).comp UnaryResources.inc_computes).comp RawUnary.run_computes)).append (const_computes _))
lemma bword_pack (q a : ℕ) : bword (pack q a)=List.replicate (exponent a) true := by
  simp only [bword,pack,discardPrefix_pairBits,UnaryResources.lengthBits_eq,List.length_replicate,
    UnaryResources.inc,value_bits,RawUnary.run,Nat.size_eq_bits_len,UnaryResources.copies_replicate,
    ←List.replicate_add,exponent]
noncomputable def tbits (x : List Bool) : List Bool := NaturalArray.exponentiate (pairBits (bword x,(2:ℕ).bits))
noncomputable def tbits_computes : PolyComputes tbits :=
  (bword_computes.pair (const_computes _)).comp NaturalArray.exponentiate_computes
lemma tbits_pack (q a : ℕ) : tbits (pack q a)=(steps a).bits := by
  rw [tbits,bword_pack,NaturalArray.exponentiate_pair,List.length_replicate]; rfl
attribute [local irreducible] bword tbits RawTake.run RawUnary.run NaturalArray.exponentiate
noncomputable def qnext (x : List Bool) : List Bool := UnaryResources.inc (UnaryResources.lengthBits (extractPrefix x))
noncomputable def anext (x : List Bool) : List Bool := UnaryResources.inc (UnaryResources.lengthBits (discardPrefix x))
noncomputable def qnext_computes : PolyComputes qnext := (extractPrefix_computes.comp UnaryResources.lengthBits_computes).comp UnaryResources.inc_computes
noncomputable def anext_computes : PolyComputes anext := (discardPrefix_computes.comp UnaryResources.lengthBits_computes).comp UnaryResources.inc_computes
attribute [local irreducible] qnext anext
noncomputable def factor (x : List Bool) : List Bool := (1000000000*value (tbits x)*value (qnext x)).bits
noncomputable def factor_computes : PolyComputes factor := by
  unfold factor
  have hh:=NatOps.mul (NatOps.mul (const_computes (1000000000:ℕ).bits) tbits_computes) qnext_computes
  simpa only [value_bits] using hh
attribute [local irreducible] factor
noncomputable def lbits (x : List Bool) : List Bool := (value (factor x)*(value (anext x))^2).bits
noncomputable def lbits_computes : PolyComputes lbits := by
  unfold lbits
  have hh:=NatOps.mul factor_computes (NatOps.mul anext_computes anext_computes)
  simpa only [value_bits,pow_two] using hh
lemma lbits_pack (q a : ℕ) : lbits (pack q a)=(samples q a).bits := by
  rw [lbits,factor,tbits_pack]
  simp only [qnext,anext,pack,extractPrefix_pairBits,discardPrefix_pairBits,UnaryResources.lengthBits_eq,
    List.length_replicate,UnaryResources.inc,value_bits,samples]
noncomputable def capPoly : Polynomial ℕ := 4096000000000*(Polynomial.X+2)^5
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose _
lemma cap_length (x : List Bool) : (cap.word x).length=4096000000000*(x.length+2)^5 := by
  rw [cap.word_length]; simp only [capPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X]
attribute [local irreducible] cap
noncomputable def unary (w : List Bool→List Bool) (x : List Bool) : List Bool := RawUnary.run (RawTake.run (pairBits (w x,cap.word x)))
noncomputable def unary_computes {w : List Bool→List Bool} (hw : PolyComputes w) : PolyComputes (unary w) :=
  ((hw.pair cap.computes).comp RawTake.run_computes).comp RawUnary.run_computes
lemma unary_eq {w : List Bool→List Bool} {x : List Bool} {n : ℕ} (hw : w x=n.bits)
    (hn : n≤4096000000000*(x.length+2)^5) : unary w x=List.replicate n true := by
  rw [unary,hw,RawTake.run_pack]
  simp only [RawUnary.run,List.length_take,cap_length,Nat.min_eq_left hn]
lemma dimensions (q a : ℕ) : q≤(pack q a).length ∧ a≤(pack q a).length := by
  simp only [pack,pairBits,List.length_append,List.length_flatMap,List.length_cons,List.length_nil,
    List.map_const',List.sum_replicate,List.length_replicate,smul_eq_mul]
  omega
lemma sample_bound (q a : ℕ) : samples q a ≤4096000000000*((pack q a).length+2)^5 := by
  obtain ⟨hq,ha⟩:=dimensions q a
  have ht:=steps_upper a
  unfold samples
  calc
    _ ≤ 1000000000*(4096*((pack q a).length+2)^2)*((pack q a).length+2)*((pack q a).length+2)^2 := by
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul
        · apply Nat.mul_le_mul_left
          exact ht.trans (by gcongr)
        · omega
      · gcongr; omega
    _ = _ := by ring
noncomputable def tword := unary tbits
noncomputable def lword := unary lbits
noncomputable def tword_computes : PolyComputes tword := unary_computes tbits_computes
noncomputable def lword_computes : PolyComputes lword := unary_computes lbits_computes
lemma lword_pack (q a : ℕ) : lword (pack q a)=List.replicate (samples q a) true := unary_eq (lbits_pack q a) (sample_bound q a)
lemma tword_pack (q a : ℕ) : tword (pack q a)=List.replicate (steps a) true := by
  apply unary_eq (tbits_pack q a)
  apply le_trans _ (sample_bound q a)
  unfold samples
  have hs:1≤(q+1)*(a+1)^2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc
    steps a = steps a*1 := by omega
    _ ≤ steps a*((q+1)*(a+1)^2) := Nat.mul_le_mul_left _ hs
    _ ≤ 1000000000*steps a*(q+1)*(a+1)^2 := by nlinarith
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources

end OAI
