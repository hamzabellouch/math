import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.BisectionMachine
import OAI.Combinatorics.KMedianRecovery.Branching.FavorableReady

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed BinaryObservableBranch
abbrev completionCount (n p : ℕ) :=
  BinaryCategorical.Tape.M (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p)+
    BinaryCategorical.Tape.K p (Categorical.Explicit.exponent p)
abbrev colorCount (n : ℕ) := n*2
abbrev labelCount (n b : ℕ) := n*Nat.clog 2 b
abbrev count (n b p : ℕ) := (colorCount n+labelCount n b)+completionCount n p
abbrev Seed (n b p : ℕ) := ((Fin n→Fin 4)×(Fin n→Fin (ColorLabel.labelRange b)))×Bits n p
def split (a b : ℕ) : (Fin (a+b)→Bool)≃(Fin a→Bool)×(Fin b→Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
def colors (n : ℕ) : (Fin (colorCount n)→Bool)≃(Fin n→Fin 4) :=
  (tensorEquiv [n] 2).trans (Equiv.arrowCongr (Equiv.refl (Fin n)) (Categorical.uniformBits 2))
def labels (n b : ℕ) : (Fin (labelCount n b)→Bool)≃(Fin n→Fin (ColorLabel.labelRange b)) :=
  (tensorEquiv [n] (Nat.clog 2 b)).trans (Equiv.arrowCongr (Equiv.refl (Fin n)) (Categorical.uniformBits (Nat.clog 2 b)))
def layout (n b p : ℕ) : (Fin (count n b p)→Bool)≃Seed n b p :=
  (split (colorCount n+labelCount n b) (completionCount n p)).trans
    (Equiv.prodCongr ((split (colorCount n) (labelCount n b)).trans
      (Equiv.prodCongr (colors n) (labels n b)))
      (BinaryCategorical.Tape.layout (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p)))
def colorTensor {n : ℕ} (s : Fin n→Fin 4) : Tensor [n] 2 := fun i=>(Categorical.uniformBits 2).symm (s i)
def labelTensor {n b : ℕ} (s : Fin n→Fin (ColorLabel.labelRange b)) : Tensor [n] (Nat.clog 2 b) :=
  fun i=>(Categorical.uniformBits (Nat.clog 2 b)).symm (s i)
def raw {n b p : ℕ} (s : Seed n b p) : List Bool :=
  (BinarySeed.raw (colorTensor s.1.1)++BinarySeed.raw (labelTensor s.1.2))++
    BinaryCategorical.Tape.raw (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p) s.2
lemma colorTensor_colors (n : ℕ) (s : Fin (colorCount n)→Bool) :
    colorTensor (colors n s)=tensorEquiv [n] 2 s := by
  funext i
  exact Equiv.symm_apply_apply _ _
lemma labelTensor_labels (n b : ℕ) (s : Fin (labelCount n b)→Bool) :
    labelTensor (labels n b s)=tensorEquiv [n] (Nat.clog 2 b) s := by
  funext i
  exact Equiv.symm_apply_apply _ _
lemma raw_colors (n : ℕ) (s : Fin (colorCount n)→Bool) :
    BinarySeed.raw (colorTensor (colors n s))=List.ofFn s := by
  rw [colorTensor_colors]
  exact raw_tensorEquiv [n] 2 s
lemma raw_labels (n b : ℕ) (s : Fin (labelCount n b)→Bool) :
    BinarySeed.raw (labelTensor (labels n b s))=List.ofFn s := by
  rw [labelTensor_labels]
  exact raw_tensorEquiv [n] (Nat.clog 2 b) s
lemma split_raw (a b : ℕ) (s : Fin (a+b)→Bool) :
    List.ofFn ((split a b s).1)++List.ofFn ((split a b s).2)=List.ofFn s := by
  rw [List.ofFn_add]
  rfl
lemma raw_layout (n b p : ℕ) (s : Fin (count n b p)→Bool) : raw (layout n b p s)=List.ofFn s := by
  unfold raw layout
  simp only [Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,raw_colors,raw_labels,
    BinaryCategorical.Tape.raw_layout]
  rw [split_raw,split_raw]
lemma probability_layout (n b p : ℕ) (P : Seed n b p→Prop) :
    FiniteSampling.probability (fun s=>P (layout n b p s))=FiniteSampling.probability P :=
  FiniteSampling.probability_comp_equiv (layout n b p) P
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRandomize
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Count.run BinaryBisection.logWord RawTake.run RawDrop.run BinaryColorLabel.colors BinaryColorLabel.labels
noncomputable def nword (x : List Bool) : List Bool := Count.run (field 0 x)
noncomputable def nword_computes : PolyComputes nword := (field_computes 0).comp Count.run_computes
noncomputable def mword (x : List Bool) : List Bool := Count.run (field 8 x)
noncomputable def mword_computes : PolyComputes mword := (field_computes 8).comp Count.run_computes
noncomputable def blog (x : List Bool) : List Bool := BinaryBisection.logWord (lengthBits (field 8 x))
noncomputable def blog_computes : PolyComputes blog := ((field_computes 8).comp lengthBits_computes).comp BinaryBisection.logWord_computes
noncomputable def cshape (x : List Bool) : List Bool := encode [nword x,[true,true]]
noncomputable def cshape_computes : PolyComputes cshape := cons_computes nword_computes (cons_computes (const_computes _) (const_computes []))
noncomputable def lshape (x : List Bool) : List Bool := encode [nword x,blog x]
noncomputable def lshape_computes : PolyComputes lshape := cons_computes nword_computes (cons_computes blog_computes (const_computes []))
noncomputable def csize (x : List Bool) : List Bool := (value (UnaryResources.lengthBits (nword x))*2).bits
noncomputable def csize_computes : PolyComputes csize := by
  unfold csize
  simpa only [value_bits,Function.comp_def] using NatOps.mul (nword_computes.comp UnaryResources.lengthBits_computes) (const_computes (2:ℕ).bits)
noncomputable def lsize (x : List Bool) : List Bool :=
  (value (UnaryResources.lengthBits (nword x))*value (UnaryResources.lengthBits (blog x))).bits
noncomputable def lsize_computes : PolyComputes lsize := by
  unfold lsize
  simpa only [Function.comp_def] using NatOps.mul (nword_computes.comp UnaryResources.lengthBits_computes) (blog_computes.comp UnaryResources.lengthBits_computes)
noncomputable def craw (x : List Bool) : List Bool := RawTake.run (pairBits (csize (extractPrefix x),discardPrefix x))
noncomputable def craw_computes : PolyComputes craw :=
  ((extractPrefix_computes.comp csize_computes).pair discardPrefix_computes).comp RawTake.run_computes
noncomputable def rest (x : List Bool) : List Bool := RawDrop.run (pairBits (csize (extractPrefix x),discardPrefix x))
noncomputable def rest_computes : PolyComputes rest :=
  ((extractPrefix_computes.comp csize_computes).pair discardPrefix_computes).comp RawDrop.run_computes
noncomputable def lraw (x : List Bool) : List Bool := RawTake.run (pairBits (lsize (extractPrefix x),rest x))
noncomputable def lraw_computes : PolyComputes lraw :=
  ((extractPrefix_computes.comp lsize_computes).pair rest_computes).comp RawTake.run_computes
noncomputable def tailBits (x : List Bool) : List Bool := RawDrop.run (pairBits (lsize (extractPrefix x),rest x))
noncomputable def tailBits_computes : PolyComputes tailBits :=
  ((extractPrefix_computes.comp lsize_computes).pair rest_computes).comp RawDrop.run_computes
noncomputable def colors (x : List Bool) : List Bool := BinaryColorLabel.colors (pairBits (cshape (extractPrefix x),craw x))
noncomputable def colors_computes : PolyComputes colors :=
  ((extractPrefix_computes.comp cshape_computes).pair craw_computes).comp BinaryColorLabel.colors_computes
noncomputable def labels (x : List Bool) : List Bool := BinaryColorLabel.labels
  (pairBits (lengthBits (field 8 (extractPrefix x)),pairBits (lshape (extractPrefix x),lraw x)))
noncomputable def labels_computes : PolyComputes labels :=
  (((extractPrefix_computes.comp (field_computes 8)).comp lengthBits_computes).pair
    ((extractPrefix_computes.comp lshape_computes).pair lraw_computes)).comp BinaryColorLabel.labels_computes
noncomputable def context (x : List Bool) : List Bool :=
  encode [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),field 3 (extractPrefix x),
    field 4 (extractPrefix x),field 5 (extractPrefix x),colors x,labels x,field 8 (extractPrefix x),
    field 9 (extractPrefix x),field 10 (extractPrefix x),field 11 (extractPrefix x)]
noncomputable def context_computes : PolyComputes context :=
  cons_computes (extractPrefix_computes.comp (field_computes 0)) (cons_computes (extractPrefix_computes.comp (field_computes 1)) (cons_computes (extractPrefix_computes.comp (field_computes 2)) (cons_computes (extractPrefix_computes.comp (field_computes 3)) (cons_computes (extractPrefix_computes.comp (field_computes 4)) (cons_computes (extractPrefix_computes.comp (field_computes 5)) (cons_computes (colors_computes) (cons_computes (labels_computes) (cons_computes (extractPrefix_computes.comp (field_computes 8)) (cons_computes (extractPrefix_computes.comp (field_computes 9)) (cons_computes (extractPrefix_computes.comp (field_computes 10)) (cons_computes (extractPrefix_computes.comp (field_computes 11)) (const_computes []))))))))))))
section Exact
variable {n m : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors0 : Fin n→Fin 3) (label0 : Fin n→Fin m) (q c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors0 label0 q c extra
lemma nword_pack : nword data=List.replicate n true := by
  simp only [nword,pack,field_encode,List.getElem?_cons_zero,Option.getD_some,RationalMatrix.encode,Count.run_encode,List.length_ofFn]
lemma mword_pack : mword data=List.replicate m true := by
  simp only [mword,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.table,Count.run_encode,List.length_ofFn]
lemma blog_pack : blog data=List.replicate (Nat.clog 2 m) true := by
  simp only [blog,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.table,lengthBits_encode,List.length_ofFn,BinaryBisection.logWord_eq,value_bits]
lemma csize_pack : csize data=(BinaryBranchTape.colorCount n).bits := by
  rw [csize,nword_pack,UnaryResources.lengthBits_eq,List.length_replicate,value_bits]
lemma lsize_pack : lsize data=(BinaryBranchTape.labelCount n m).bits := by
  rw [lsize,nword_pack,blog_pack]
  simp only [UnaryResources.lengthBits_eq,List.length_replicate,value_bits]
lemma cshape_pack : cshape data=BinarySeed.shape [n,2] := by rw [cshape,nword_pack]; rfl
lemma lshape_pack : lshape data=BinarySeed.shape [n,Nat.clog 2 m] := by rw [lshape,nword_pack,blog_pack]; rfl
variable (seed : BinaryBranchTape.Seed n m s.leaves.length)
local notation "input" => pairBits (data,BinaryBranchTape.raw seed)
lemma craw_pack : craw input=BinarySeed.raw (BinaryBranchTape.colorTensor seed.1.1) := by
  rw [craw,extractPrefix_pairBits,discardPrefix_pairBits,csize_pack,RawTake.run_pack]
  have hc : (BinarySeed.raw (BinaryBranchTape.colorTensor seed.1.1)).length=BinaryBranchTape.colorCount n := by
    simp only [BinarySeed.raw_length,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Nat.mul_one]
  rw [BinaryBranchTape.raw,List.append_assoc,←hc,List.take_left]
lemma rest_pack : rest input=BinarySeed.raw (BinaryBranchTape.labelTensor seed.1.2)++
    BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) seed.2 := by
  rw [rest,extractPrefix_pairBits,discardPrefix_pairBits,csize_pack,RawDrop.run_encode]
  have hc : (BinarySeed.raw (BinaryBranchTape.colorTensor seed.1.1)).length=BinaryBranchTape.colorCount n := by
    simp only [BinarySeed.raw_length,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Nat.mul_one]
  rw [BinaryBranchTape.raw,List.append_assoc,←hc,List.drop_left]
lemma lraw_pack : lraw input=BinarySeed.raw (BinaryBranchTape.labelTensor seed.1.2) := by
  rw [lraw,extractPrefix_pairBits,lsize_pack,rest_pack,RawTake.run_pack]
  have hl : (BinarySeed.raw (BinaryBranchTape.labelTensor seed.1.2)).length=BinaryBranchTape.labelCount n m := by
    simp only [BinarySeed.raw_length,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Nat.mul_one]
  rw [←hl,List.take_left]
lemma tailBits_pack : tailBits input=
    BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) seed.2 := by
  rw [tailBits,extractPrefix_pairBits,lsize_pack,rest_pack,RawDrop.run_encode]
  have hl : (BinarySeed.raw (BinaryBranchTape.labelTensor seed.1.2)).length=BinaryBranchTape.labelCount n m := by
    simp only [BinarySeed.raw_length,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,Nat.mul_one]
  rw [←hl,List.drop_left]
lemma colors_pack : colors input=BinaryFinSet.table (fun i=>ColorLabel.color (seed.1.1 i)) := by
  rw [colors,extractPrefix_pairBits,cshape_pack,craw_pack]
  simpa only [BinaryBranchTape.colorTensor,Equiv.apply_symm_apply] using
    BinaryColorLabel.colors_tensor (BinaryBranchTape.colorTensor seed.1.1)
lemma labels_pack (hm : 0 < m) : labels input=BinaryFinSet.table (fun i=>ColorLabel.label m hm (seed.1.2 i)) := by
  rw [labels,extractPrefix_pairBits,lshape_pack,lraw_pack]
  have hh : lengthBits (field 8 data)=m.bits := by
    simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryFinSet.table,
      lengthBits_encode,List.length_ofFn]
  rw [hh]
  refine (BinaryColorLabel.labels_tensor m hm (BinaryBranchTape.labelTensor seed.1.2)).trans ?_
  congr 1
  funext i
  apply congrArg (ColorLabel.label m hm)
  exact Equiv.apply_symm_apply (Categorical.uniformBits (Nat.clog 2 m)) (seed.1.2 i)
lemma context_pack (hm : 0 < m) : context input=
    pack δ D F S Δ s (fun i=>ColorLabel.color (seed.1.1 i)) (fun i=>ColorLabel.label m hm (seed.1.2 i)) q c extra := by
  rw [context,colors_pack,labels_pack δ D F S Δ s colors0 label0 q c extra seed hm]
  simp only [extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
end Exact
end MetricKMedianRecovery.BitMachine.BinaryBranchRandomize

end OAI
