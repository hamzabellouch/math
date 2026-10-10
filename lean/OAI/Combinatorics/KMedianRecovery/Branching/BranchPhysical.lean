import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionFair

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ}
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => BinaryBranchContext.pack δ D F S Δ s colors label k c extra
local notation "blue" => Finset.filter (fun i=>colors i=2) (S\RationalSampling.State.deleted s)
local notation "red" => Finset.filter (fun i=>colors i=1) (S\RationalSampling.State.deleted s)
local notation "green" => Finset.filter (fun i=>colors i=0) (S\RationalSampling.State.deleted s)
local notation "score" => (fun u v=>RationalSampling.assignmentWeight δ D S Δ s u*δ u v)
lemma plan_pack (d : ℕ) (r0 y0 : Fin n) (v : ℚ) (xs : List (BlueDP.Atom (Fin m) (Fin n) (Fin n)))
    (h : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs))
    (hcap : 2^m*(2*(BinaryFinSet.encode (Finset.univ : Finset (Fin m))).length+2)≤
      (pairBits (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c,
        BinaryFinSet.encode (Finset.univ : Finset (Fin m)))).length.succ^d) :
    plan d data=encode [BinaryFinSet.table (BlueDP.makePlan blue F label score c r0 y0 v xs h).sel,
      BinaryFinSet.table (BlueDP.makePlan blue F label score c r0 y0 v xs h).dst] := by
  rw [plan,best,bluePack_pack]
  rw [BinaryBlueProgram.run_pack d extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c (by simpa using hcap)]
  simp only [BinaryBranchContext.pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  exact BinaryBlueOutput.run_best _ _ _ _ _ _ _ _ _ h
variable (hH : ∀ i,(balls δ F s i).Nonempty)
local notation "loc" => Completion.CopyGround.location (balls δ F s) hH
local notation "wt" => (fun i=>RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i))
local notation "rb" => (fun i=>RationalSampling.reference δ green Δ (RationalSampling.State.mk ∅ (RationalSampling.State.leaves s)) (SortedIndex.enum red i))
local notation "bas" => (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
local notation "dst" => (fun i e=>δ (SortedIndex.enum D i) (loc e))
local notation "rd" => (fun i e=>δ (SortedIndex.enum red i) (loc e))
variable (d : ℕ) (sel dest : Fin m→Fin n)
local notation "compData" => BinaryCompletionRealize.pack F S s.deleted Completion.CopyGround.part
  (Completion.CopyGround.origin (balls δ F s) hH) loc (SortedIndex.enum red) sel dest k bas dst wt rb rd []
lemma completion_pack (hp : plan d data=encode [BinaryFinSet.table sel,BinaryFinSet.table dest]) : completion d data=compData := by
  have hc:=classOf_pack δ D F S Δ s colors label k c extra (1:Fin 3)
  change classOf 1 data=_ at hc
  rw [completion,hp,parts_pack,origins_pack δ D F S Δ s colors label k c extra hH,
    locations_pack δ D F S Δ s colors label k c extra hH,hc,
    rows_pack δ D F S Δ s colors label k c extra hH]
  simp only [BinaryBranchContext.pack,BinaryCompletionRealize.pack,field_encode,List.getElem?_cons_succ,
    List.getElem?_cons_zero,Option.getD_some,BinarySamplingState.encode,extractPrefix_pairBits,BinaryFinSet.table_enum]
  rfl
lemma run_pack (hp : plan d data=encode [BinaryFinSet.table sel,BinaryFinSet.table dest])
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length
      (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) :
    run d (pairBits (data,BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length
      (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
      BinaryFinSet.encode (BinaryCompletionFair.result F S s.deleted Completion.CopyGround.part
        (Completion.CopyGround.part_surjective (balls δ F s) hH) (Completion.CopyGround.origin (balls δ F s) hH)
        loc (SortedIndex.enum red) sel dest k bas dst wt rb rd bits) := by
  rw [run,extractPrefix_pairBits,discardPrefix_pairBits,
    completion_pack δ D F S Δ s colors label k c extra hH d sel dest hp]
  exact BinaryCompletionFair.run_pack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bits
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

namespace MetricKMedianRecovery.BitMachine.BinaryBranchCheck
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
def Ready (δ : Fin n→Fin n→ℚ) (F S : Finset (Fin n)) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q c m : ℕ) : Prop :=
  s.deleted⊆S ∧ (∀ i,(balls δ F s i).Nonempty) ∧ (∀ z∈s.leaves,0≤z.2) ∧
    q≤((S\s.deleted).filter (fun i=>colors i=1)).card ∧ s.leaves.length+c≤ s.deleted.card+q+m
noncomputable def outside (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (extractPrefix (field 5 x),field 3 x))
noncomputable def outside_computes : PolyComputes outside :=
  (((field_computes 5).comp extractPrefix_computes).pair (field_computes 3)).comp BinaryNatSet.diff_computes
noncomputable def badBall (x : List Bool) : Bool := decide (discardPrefix x=[])
noncomputable def badBall_computes : PolyComputes (fun x=>[badBall x]) := discardPrefix_computes.comp isEmpty_computes
noncomputable def badBalls (x : List Bool) : List Bool := filterWith badBall (pairBits ([],field 1 (copyData x)))
noncomputable def badBalls_computes : PolyComputes badBalls :=
  ((const_computes []).pair (copyData_computes.comp (field_computes 1))).comp (filterWith_computes badBall_computes)
noncomputable def badRadius (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix (discardPrefix x))<0)
noncomputable def badRadius_computes : PolyComputes (fun x=>[badRadius x]) :=
  RatOps.lt (RatOps.ofWords (discardPrefix_computes.comp discardPrefix_computes)) (RatOps.const 0)
noncomputable def badRadii (x : List Bool) : List Bool := filterWith badRadius (pairBits ([],discardPrefix (field 5 x)))
noncomputable def badRadii_computes : PolyComputes badRadii :=
  ((const_computes []).pair ((field_computes 5).comp discardPrefix_computes)).comp (filterWith_computes badRadius_computes)
noncomputable def lhs (x : List Bool) : List Bool := (value (lengthBits (discardPrefix (field 5 x)))+(field 10 x).length).bits
noncomputable def lhs_computes : PolyComputes lhs := by
  unfold lhs
  simpa only [lhs,Function.comp_def,UnaryResources.lengthBits_eq,value_bits] using NatOps.add (((field_computes 5).comp discardPrefix_computes).comp lengthBits_computes)
    ((field_computes 10).comp UnaryResources.lengthBits_computes)
noncomputable def rhs (x : List Bool) : List Bool :=
  (value (lengthBits (extractPrefix (field 5 x)))+value (field 9 x)+value (lengthBits (field 8 x))).bits
noncomputable def rhs_computes : PolyComputes rhs := by
  unfold rhs
  simpa only [rhs,Function.comp_def,value_bits] using NatOps.add (NatOps.add (((field_computes 5).comp extractPrefix_computes).comp lengthBits_computes) (field_computes 9))
    ((field_computes 8).comp lengthBits_computes)
noncomputable def run (x : List Bool) : Bool :=
  decide (outside x=[] ∧ badBalls x=[] ∧ badRadii x=[] ∧ value (field 9 x)≤value (lengthBits (classOf 1 x)) ∧ value (lhs x)≤value (rhs x))
noncomputable def run_computes : PolyComputes (fun x=>[run x]) := by
  simpa only [run,Bool.decide_and,Function.comp_def] using
    (outside_computes.comp isEmpty_computes).and ((badBalls_computes.comp isEmpty_computes).and
      ((badRadii_computes.comp isEmpty_computes).and ((NatOps.le (field_computes 9) ((classOf_computes 1).comp lengthBits_computes)).and
        (NatOps.le lhs_computes rhs_computes))))
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors label k c extra
lemma outside_pack : outside data=BinaryFinSet.encode (s.deleted\S) := by
  simp only [outside,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingState.encode,extractPrefix_pairBits,BinaryFinSet.diff_pack]
lemma badBalls_pack : badBalls data=encode ((List.ofFn (fun i=>BinaryFinSet.encode (balls δ F s i))).filter (fun w=>decide (w=[]))) := by
  rw [badBalls,copyData_pack]
  simp only [BinaryCopyTables.pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,filterWith_encode,badBall,
    discardPrefix_pairBits]
lemma badRadii_pack : badRadii data=BinaryNearestLeaf.leavesBits (s.leaves.filter (fun z=>decide (z.2<0))) := by
  simp only [badRadii,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingState.encode,discardPrefix_pairBits,BinaryNearestLeaf.leavesBits,filterWith_encode,List.filter_map,Function.comp_def,
    badRadius,BinarySamplingReference.leafBits,discardPrefix_pairBits,BinaryRational.decode_encode]
lemma lhs_pack : lhs data=(s.leaves.length+c).bits := by
  simp only [lhs,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingState.encode,discardPrefix_pairBits,BinaryNearestLeaf.leavesBits,lengthBits_encode,List.length_map,value_bits,List.length_replicate]
lemma rhs_pack : rhs data=(s.deleted.card+k+m).bits := by
  simp only [rhs,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingState.encode,extractPrefix_pairBits,BinaryFinSet.encode_lengthBits,BinaryFinSet.table,lengthBits_encode,List.length_ofFn,value_bits]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

end OAI
