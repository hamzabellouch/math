import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchSeedLayout

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
lemma source_run (A : ℝ) : ∃ d : ℕ, ∀ {n m : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (label : Fin n→Fin m) (q c : ℕ) (extra : List Bool) (r0 y0 : Fin n) (N : ℕ),
    N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
    ∀ bits,
    run d (pairBits (pack δ D F S Δ s colors label q c extra,
      BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
        (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
    BinaryFinSet.encode (output δ D F S Δ s colors label q c r0 y0 bits) := by
  obtain ⟨d,hd⟩:=BinaryBlueStates.source_capacity A
  refine ⟨d,?_⟩
  intro n m δ D F S Δ s colors label q c extra r0 y0 N hN hm bits
  apply run_pack δ D F S Δ s colors label q c extra d r0 y0 _ bits
  have hx:=hd (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits)
    ((S\s.deleted).filter (fun i=>colors i=2)) F label (rationalScore δ D S Δ s) Finset.univ c)
      (Finset.univ : Finset (Fin m)) N
  apply (by simpa only [Finset.card_univ,Fintype.card_fin] using hx)
  · have he : extra.length≤(BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits)
        ((S\s.deleted).filter (fun i=>colors i=2)) F label (rationalScore δ D S Δ s) Finset.univ c).length :=
      member_length (by simp)
    simp only [pairBits_length]
    omega
  · exact hm
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch
open WordOperations WordList BinaryBranchContext BinaryObservableBranch
noncomputable def run (d : ℕ) (x : List Bool) : List Bool :=
  BinaryObservableBranch.run d (pairBits (BinaryBranchRandomize.context x,BinaryBranchRandomize.tailBits x))
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) :=
  (BinaryBranchRandomize.context_computes.pair BinaryBranchRandomize.tailBits_computes).comp
    (BinaryObservableBranch.run_computes d)
lemma source_run (A : ℝ) : ∃ d : ℕ, ∀ {n b : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (colors0 : Fin n→Fin 3)
    (label0 : Fin n→Fin b) (q c : ℕ) (extra : List Bool) (r0 y0 : Fin n) (N : ℕ),
    N≤extra.length → (b:ℝ)≤A*Real.log ((N:ℝ)+2) → (hb0 : 0<b) →
    ∀ seed : BinaryBranchTape.Seed n b s.leaves.length,
    run d (pairBits (pack δ D F S Δ s colors0 label0 q c extra,BinaryBranchTape.raw seed))=
    BinaryFinSet.encode (output δ D F S Δ s (fun i=>ColorLabel.color (seed.1.1 i))
      (fun i=>ColorLabel.label b hb0 (seed.1.2 i)) q c r0 y0 seed.2) := by
  obtain ⟨d,hd⟩:=BinaryObservableBranch.source_run A
  refine ⟨d,?_⟩
  intro n b δ D F S Δ s colors0 label0 q c extra r0 y0 N hN hb hb0 seed
  rw [run,BinaryBranchRandomize.context_pack δ D F S Δ s colors0 label0 q c extra seed hb0,
    BinaryBranchRandomize.tailBits_pack]
  exact hd δ D F S Δ s _ _ q c extra r0 y0 N hN hb seed.2
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram BinaryArithmetic
attribute [local instance] Classical.propDecidable
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q : ℕ) (extra : List Bool) : List Bool :=
  BinaryBranchContext.pack δ D F S Δ s colors (fun _=>0 : Fin n→Fin 1) q 0 extra
noncomputable def rhs (x : List Bool) : List Bool :=
  (value (lengthBits (extractPrefix (field 5 x)))+value (field 9 x)).bits
noncomputable def rhs_computes : PolyComputes rhs := by
  unfold rhs
  simpa only [Function.comp_def,value_bits] using
    NatOps.add (((field_computes 5).comp extractPrefix_computes).comp lengthBits_computes) (field_computes 9)
noncomputable def check (x : List Bool) : Bool :=
  decide (BinaryBranchCheck.outside x=[] ∧ BinaryBranchCheck.badBalls x=[] ∧ BinaryBranchCheck.badRadii x=[] ∧
    value (field 9 x)≤value (lengthBits (classOf 1 x)) ∧ value (BinaryBranchCheck.lhs x)≤value (rhs x))
noncomputable def check_computes : PolyComputes (fun x=>[check x]) := by
  simpa only [check,Bool.decide_and,Function.comp_def] using
    (BinaryBranchCheck.outside_computes.comp isEmpty_computes).and
      ((BinaryBranchCheck.badBalls_computes.comp isEmpty_computes).and
        ((BinaryBranchCheck.badRadii_computes.comp isEmpty_computes).and
          ((NatOps.le (field_computes 9) ((classOf_computes 1).comp lengthBits_computes)).and
            (NatOps.le BinaryBranchCheck.lhs_computes rhs_computes))))
noncomputable def completion (x : List Bool) : List Bool :=
  encode [field 2 x,field 3 x,extractPrefix (field 5 x),parts x,origins x,locations x,classOf 1 x,[],[],[],rows x]
noncomputable def completion_computes : PolyComputes completion :=
  cons_computes (field_computes 2) (cons_computes (field_computes 3)
    (cons_computes ((field_computes 5).comp extractPrefix_computes) (cons_computes parts_computes
      (cons_computes origins_computes (cons_computes locations_computes (cons_computes (classOf_computes 1)
        (cons_computes (const_computes []) (cons_computes (const_computes [])
          (cons_computes (const_computes []) (cons_computes rows_computes (const_computes [])))))))))))
noncomputable def run (x : List Bool) : List Bool :=
  if check (extractPrefix x) then
    BinaryCompletionFair.run (pairBits (completion (extractPrefix x),discardPrefix x))
  else field 3 (extractPrefix x)
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def] using
    (extractPrefix_computes.comp check_computes).cond
      (((extractPrefix_computes.comp completion_computes).pair discardPrefix_computes).comp BinaryCompletionFair.run_computes)
      (extractPrefix_computes.comp (field_computes 3))
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q : ℕ)
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) : Finset (Fin n) := by
  classical
  exact if hr : BinaryBranchCheck.Ready δ F S s colors q 0 0 then
    result δ D F S Δ s colors hr.2.1 (Fin.elim0 : Fin 0→Fin n) Fin.elim0 q bits
  else S
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors q extra
lemma check_pack : check data=decide (BinaryBranchCheck.Ready δ F S s colors q 0 0) := by
  classical
  have hc:=classOf_pack δ D F S Δ s colors (fun _=>0 : Fin n→Fin 1) q 0 extra (1:Fin 3)
  change classOf 1 data=_ at hc
  unfold check
  apply decide_eq_decide.mpr
  unfold BinaryBranchCheck.Ready
  rw [pack,BinaryBranchCheck.outside_nil,BinaryBranchCheck.badBalls_nil,BinaryBranchCheck.badRadii_nil,
    BinaryBranchCheck.lhs_pack]
  change (_ ∧ _ ∧ _ ∧ value (field 9 data) ≤ value (lengthBits (classOf 1 data)) ∧ _)↔_
  rw [hc,BinaryFinSet.encode_lengthBits]
  simp only [rhs,pack,BinaryBranchContext.pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,
    Option.getD_some,BinarySamplingState.encode,extractPrefix_pairBits,BinaryFinSet.encode_lengthBits,value_bits,Nat.add_zero]
lemma completion_pack (hH : ∀ i,(balls δ F s i).Nonempty) :
    completion data=BinaryCompletionRealize.pack F S s.deleted Completion.CopyGround.part
      (Completion.CopyGround.origin (balls δ F s) hH) (Completion.CopyGround.location (balls δ F s) hH)
      (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1))) (Fin.elim0 : Fin 0→Fin n) Fin.elim0 q
      (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
      (fun i e=>δ (SortedIndex.enum D i) (Completion.CopyGround.location (balls δ F s) hH e))
      (fun i=>RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1)) i))
      (fun i=>RationalSampling.reference δ ((S\s.deleted).filter (fun i=>colors i=0)) Δ
        (RationalSampling.State.mk ∅ s.leaves) (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1)) i))
      (fun i e=>δ (SortedIndex.enum ((S\s.deleted).filter (fun i=>colors i=1)) i)
        (Completion.CopyGround.location (balls δ F s) hH e)) [] := by
  have hc:=classOf_pack δ D F S Δ s colors (fun _=>0 : Fin n→Fin 1) q 0 extra (1:Fin 3)
  change classOf 1 (BinaryBranchContext.pack δ D F S Δ s colors (fun _=>0 : Fin n→Fin 1) q 0 extra)=_ at hc
  rw [completion,pack,parts_pack,origins_pack δ D F S Δ s colors (fun _=>0 : Fin n→Fin 1) q 0 extra hH,
    locations_pack δ D F S Δ s colors (fun _=>0 : Fin n→Fin 1) q 0 extra hH,hc,
    rows_pack δ D F S Δ s colors (fun _=>0 : Fin n→Fin 1) q 0 extra hH]
  simp only [BinaryBranchContext.pack,BinaryCompletionRealize.pack,field_encode,List.getElem?_cons_succ,
    List.getElem?_cons_zero,Option.getD_some,BinarySamplingState.encode,extractPrefix_pairBits,BinaryFinSet.table_enum]
  rfl
lemma run_pack
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) :
    run (pairBits (data,BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length
      (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
    BinaryFinSet.encode (output δ D F S Δ s colors q bits) := by
  classical
  rw [run,extractPrefix_pairBits,discardPrefix_pairBits,check_pack]
  simp only [decide_eq_true_eq]
  unfold output
  by_cases hr : BinaryBranchCheck.Ready δ F S s colors q 0 0
  · rw [ite_eq_left hr,dite_eq_left hr,completion_pack δ D F S Δ s colors q extra hr.2.1]
    exact BinaryCompletionFair.run_pack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bits
  · rw [ite_eq_right hr,dite_eq_right hr]
    simp only [pack,BinaryBranchContext.pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
