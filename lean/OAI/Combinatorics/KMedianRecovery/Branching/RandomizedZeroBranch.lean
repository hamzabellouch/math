import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.ObservableCapacity

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch
open WordOperations WordList BinaryBranchContext
variable {n : ℕ}
noncomputable def run (x : List Bool) : List Bool := BinaryZeroBranch.run
  (pairBits (BinaryBranchRandomize.context x,BinaryBranchRandomize.tailBits x))
noncomputable def run_computes : PolyComputes run :=
  (BinaryBranchRandomize.context_computes.pair BinaryBranchRandomize.tailBits_computes).comp BinaryZeroBranch.run_computes
abbrev Seed (n p : ℕ) := (Fin n→Fin 4)×BinaryObservableBranch.Bits n p
def embed {n p : ℕ} (seed : Seed n p) : BinaryBranchTape.Seed n 1 p := ((seed.1,fun _=>⟨0,by unfold ColorLabel.labelRange; positivity⟩),seed.2)
def raw {n p : ℕ} (seed : Seed n p) : List Bool := BinaryBranchTape.raw (embed seed)
lemma run_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors0 : Fin n→Fin 3) (q : ℕ) (extra : List Bool) (seed : Seed n s.leaves.length) :
    run (pairBits (BinaryZeroBranch.pack δ D F S Δ s colors0 q extra,raw seed))=
      BinaryFinSet.encode (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed.1 i)) q seed.2) := by
  rw [run,BinaryZeroBranch.pack,raw,
    BinaryBranchRandomize.context_pack δ D F S Δ s colors0 (fun _=>0 : Fin n→Fin 1) q 0 extra (embed seed) (by omega),
    BinaryBranchRandomize.tailBits_pack]
  have he : (fun i=>ColorLabel.label 1 (by omega) ((embed seed).1.2 i))=(fun _=>0 : Fin n→Fin 1) := by
    funext i
    exact Subsingleton.elim _ _
  simp only [he]
  exact BinaryZeroBranch.run_pack δ D F S Δ s (fun i=>ColorLabel.color (seed.1 i)) q extra seed.2
abbrev count (n p : ℕ) := BinaryBranchTape.colorCount n+BinaryBranchTape.completionCount n p
def layout (n p : ℕ) : (Fin (count n p)→Bool)≃Seed n p :=
  (BinaryBranchTape.split _ _).trans (Equiv.prodCongr (BinaryBranchTape.colors n)
    (BinaryCategorical.Tape.layout (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p)))
lemma raw_eq {n p : ℕ} (seed : Seed n p) : raw seed=
    BinarySeed.raw (BinaryBranchTape.colorTensor seed.1)++BinaryCategorical.Tape.raw (p*n) p
      (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p) seed.2 := by
  have hlabel : BinarySeed.raw (BinaryBranchTape.labelTensor (embed seed).1.2)=[] := by
    apply List.eq_nil_of_length_eq_zero
    rw [BinarySeed.raw_length]
    simp [Nat.clog]
  change (BinarySeed.raw (BinaryBranchTape.colorTensor seed.1)++BinarySeed.raw (BinaryBranchTape.labelTensor (embed seed).1.2))++_= _
  rw [hlabel,List.append_nil]
  rfl
lemma raw_layout (n p : ℕ) (seed : Fin (count n p)→Bool) : raw (layout n p seed)=List.ofFn seed := by
  rw [raw_eq]
  simp only [layout,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,
    BinaryBranchTape.raw_colors,BinaryCategorical.Tape.raw_layout]
  exact BinaryBranchTape.split_raw _ _ seed
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCategorical
noncomputable def pword (x : List Bool) : List Bool := Count.run (discardPrefix (field 5 x))
noncomputable def pword_computes : PolyComputes pword := ((field_computes 5).comp discardPrefix_computes).comp Count.run_computes
noncomputable def qword (x : List Bool) : List Bool := RepeatedAppend.copies (pword x).length (BinaryBranchRandomize.nword x)
noncomputable def qword_computes : PolyComputes qword := UnaryResources.copy_computes pword_computes BinaryBranchRandomize.nword_computes
noncomputable def dimensions (x : List Bool) : List Bool := pairBits (qword x,pword x)
noncomputable def dimensions_computes : PolyComputes dimensions := qword_computes.pair pword_computes
attribute [local irreducible] dimensions Resources.tword Resources.lword Resources.bword BinarySeed.product
noncomputable def tword (x : List Bool) : List Bool := Resources.tword (dimensions x)
noncomputable def lword (x : List Bool) : List Bool := Resources.lword (dimensions x)
noncomputable def bword (x : List Bool) : List Bool := Resources.bword (dimensions x)
noncomputable def tword_computes : PolyComputes tword := dimensions_computes.comp Resources.tword_computes
noncomputable def lword_computes : PolyComputes lword := dimensions_computes.comp Resources.lword_computes
noncomputable def bword_computes : PolyComputes bword := dimensions_computes.comp Resources.bword_computes
noncomputable def leftShape (x : List Bool) : List Bool := encode [tword x,qword x,lword x,pword x,bword x]
noncomputable def rightShape (x : List Bool) : List Bool := encode [pword x,bword x]
noncomputable def leftShape_computes : PolyComputes leftShape := cons_computes tword_computes
  (cons_computes qword_computes (cons_computes lword_computes (cons_computes pword_computes (cons_computes bword_computes (const_computes [])))))
noncomputable def rightShape_computes : PolyComputes rightShape := cons_computes pword_computes (cons_computes bword_computes (const_computes []))
attribute [local irreducible] leftShape rightShape BinaryBranchRandomize.csize BinaryBranchRandomize.lsize
noncomputable def run (x : List Bool) : List Bool :=
  (value (BinaryBranchRandomize.csize x)+value (BinaryBranchRandomize.lsize x)+
    (value (BinarySeed.product 5 (leftShape x))+value (BinarySeed.product 2 (rightShape x)))).bits
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [value_bits,Function.comp_def] using NatOps.add (NatOps.add BinaryBranchRandomize.csize_computes BinaryBranchRandomize.lsize_computes)
    (NatOps.add (leftShape_computes.comp (BinarySeed.product_computes 5)) (rightShape_computes.comp (BinarySeed.product_computes 2)))
section Exact
variable {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
  (colors : Fin n→Fin 3) (label : Fin n→Fin b) (q c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors label q c extra
lemma pword_pack : pword data=List.replicate s.leaves.length true := by
  simp only [pword,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinarySamplingState.encode,discardPrefix_pairBits,BinaryNearestLeaf.leavesBits,Count.run_encode,List.length_map]
lemma qword_pack : qword data=List.replicate (s.leaves.length*n) true := by
  rw [qword,pword_pack,BinaryBranchRandomize.nword_pack,List.length_replicate,UnaryResources.copies_replicate]
lemma dimensions_pack : dimensions data=Resources.pack (s.leaves.length*n) s.leaves.length := by
  rw [dimensions,qword_pack,pword_pack]; rfl
lemma leftShape_pack : leftShape data=BinarySeed.shape [Categorical.Explicit.steps s.leaves.length,s.leaves.length*n,
    Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length,s.leaves.length,Categorical.Explicit.exponent s.leaves.length] := by
  rw [leftShape,tword,dimensions_pack,Resources.tword_pack,qword_pack,lword,dimensions_pack,Resources.lword_pack,
    pword_pack,bword,dimensions_pack,Resources.bword_pack]; rfl
lemma rightShape_pack : rightShape data=BinarySeed.shape [s.leaves.length,Categorical.Explicit.exponent s.leaves.length] := by
  rw [rightShape,pword_pack,bword,dimensions_pack,Resources.bword_pack]; rfl
lemma run_pack : run data=(count n b s.leaves.length).bits := by
  rw [run,BinaryBranchRandomize.csize_pack,BinaryBranchRandomize.lsize_pack,leftShape_pack,rightShape_pack]
  rw [show 5=[Categorical.Explicit.steps s.leaves.length,s.leaves.length*n,
    Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length,s.leaves.length,Categorical.Explicit.exponent s.leaves.length].length from rfl,
    BinarySeed.product_shape,show 2=[s.leaves.length,Categorical.Explicit.exponent s.leaves.length].length from rfl,
    BinarySeed.product_shape]
  simp only [value_bits,count,completionCount,BinaryCategorical.Tape.M,BinaryCategorical.Tape.K,BinarySeed.count,
    List.prod_cons,List.prod_nil,Nat.mul_one,Categorical.Explicit.steps]
end Exact
noncomputable def cut (x : List Bool) : List Bool := pairBits (extractPrefix x,
  RawTake.run (pairBits (run (extractPrefix x),discardPrefix x)))
attribute [local irreducible] run RawTake.run
noncomputable def cut_computes : PolyComputes cut := extractPrefix_computes.pair
  (((extractPrefix_computes.comp run_computes).pair discardPrefix_computes).comp RawTake.run_computes)
lemma cut_pack {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin b) (q c : ℕ) (extra w : List Bool) :
    cut (pairBits (pack δ D F S Δ s colors label q c extra,w))=
      pairBits (pack δ D F S Δ s colors label q c extra,w.take (count n b s.leaves.length)) := by
  simp only [cut,extractPrefix_pairBits,discardPrefix_pairBits,run_pack,RawTake.run_pack]
end MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count

end OAI
