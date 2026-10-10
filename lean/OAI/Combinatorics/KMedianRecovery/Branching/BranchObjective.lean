import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.RationalBranch

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma objective_eq_source (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (sel dest : Fin m→Fin n) (k : ℕ)
    (X : Finset (Fin (s.leaves.length*n))) :
    objective δ D F S Δ s colors hH sel dest k X=
    surrogate (∑ j,Sampling.branchScore D S (Δ:ℝ) s.real (sel j) (dest j)) k
      (fun p : D=>virtualNearest (S\s.deleted) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) p)
      (fun p e=>dist (p:Fin n) (CopyGround.location (balls δ F s) hH e))
      (fun i : Fin ((S\s.deleted).filter (fun i=>colors i=1)).card=>assignmentWeight D (Sampling.completionAssignment S (Δ:ℝ) s.real) (SortedIndex.enum _ i))
      (fun i=>virtualNearest ((S\s.deleted).filter (fun i=>colors i=0)) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) (SortedIndex.enum _ i))
      (fun i e=>dist (SortedIndex.enum _ i) (CopyGround.location (balls δ F s) hH e)) X := by
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  have hw : Sampling.leafCenter (RationalSampling.State.real (⟨∅,s.leaves⟩ : RationalSampling.State n))=Sampling.leafCenter s.real := rfl
  have hr : Sampling.leafRadius (RationalSampling.State.real (⟨∅,s.leaves⟩ : RationalSampling.State n))=Sampling.leafRadius s.real := rfl
  simp only [RationalSampling.State.real] at hw hr
  unfold objective
  simp only [Rat.cast_mul,hδ,RationalSampling.assignmentWeight_cast δ hδ,
    RationalSampling.reference_cast δ hδ,Sampling.reference_eq_virtualNearest,
    RationalSampling.State.real,Finset.sdiff_empty,Sampling.branchScore]
  rw [hw,hr]
  have hh:=surrogate_reindex (SortedIndex.equiv D) (Equiv.refl (Fin red.card))
    (∑ j,Sampling.branchScore D S (Δ:ℝ) s.real (sel j) (dest j)) k
    (fun p : D=>virtualNearest (S\s.deleted) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) p)
    (fun p e=>dist (p:Fin n) (CopyGround.location (balls δ F s) hH e))
    (fun i : Fin red.card=>assignmentWeight D (Sampling.completionAssignment S (Δ:ℝ) s.real) (SortedIndex.enum red i))
    (fun i=>virtualNearest green (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) (SortedIndex.enum red i))
    (fun i e=>dist (SortedIndex.enum red i) (CopyGround.location (balls δ F s) hH e)) X
  simpa only [Function.comp_def,Equiv.refl_apply,SortedIndex.equiv_val,Sampling.branchScore,
    RationalSampling.State.real,red,green] using hh
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

namespace BlueSubsetDP
variable {R Y L : Type*} [DecidableEq R] [DecidableEq Y] [DecidableEq L] [Fintype L]
def Plan.reweight {B : Finset R} {F : Finset Y} {label : R→L} {q : R→Y→ℝ} {c : ℕ}
    (P : Plan B F label q c) (q' : R→Y→ℝ) (h : q'=q) : Plan B F label q' c :=
  ⟨P.sel,P.dst,P.selection,P.selected_injective,P.destination_count,by simpa only [h] using P.value_eq⟩
end BlueSubsetDP
namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext Sampling
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
noncomputable def rationalScore (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (u v : Fin n) : ℚ :=
  RationalSampling.assignmentWeight δ D S Δ s u*δ u v
lemma score_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) :
    (fun u v=>(rationalScore δ D S Δ s u v:ℝ))=branchScore D S (Δ:ℝ) s.real := by
  funext u v
  simp only [rationalScore,branchScore,Rat.cast_mul,hδ,RationalSampling.assignmentWeight_cast δ hδ]
lemma favorable_literal_plan [Nonempty (Fin n)]
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty) (hOF : O⊆F)
    (Δ : ℚ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)) u)
    (label : Fin n→Fin m)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
    (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)))))
    (r0 y0 : Fin n) :
    let blue:=(S\s.deleted).filter (fun i=>colors i=2)
    let score:=rationalScore δ D S Δ s
    let bd:=designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))
    let c:=(bd.image (C.blueDestination hD s.real (19/50))).card
    ∃ v xs,∃ h : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs),
      let P:=BlueDP.makePlan blue F label score c r0 y0 v xs h
      (∑ l,branchScore D S (Δ:ℝ) s.real (P.sel l) (P.dst l))≤
        ∑ u∈bd,assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
          minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
            (C.destinations s.real) (C.destinations_nonempty hD s.real) u := by
  classical
  dsimp only
  obtain ⟨P0,hP0,hvalue⟩:=C.favorable_computedPlan hD s.real (19/50) (Δ:ℝ) F hOF colors hcolors label
    (by simpa only [Fintype.card_fin] using hcard) hinj
  clear hP0
  change BlueSubsetDP.Plan ((S\s.deleted).filter (fun i=>colors i=2)) F label
    (branchScore D S (Δ:ℝ) s.real) _ at P0
  let P0':=P0.reweight (fun u v=>(rationalScore δ D S Δ s u v:ℝ)) (score_cast δ hδ D S Δ s)
  obtain ⟨v,xs,h⟩:=BlueDP.best_some_of_plan _ _ label (rationalScore δ D S Δ s) _ P0'
  refine ⟨v,xs,h,?_⟩
  let P:=BlueDP.makePlan _ _ label (rationalScore δ D S Δ s) _ r0 y0 v xs h
  have hv:=BlueDP.plan_value_unique _ _ label (rationalScore δ D S Δ s) _ P P0'
  have he:=score_cast δ hδ D S Δ s
  have hev (u v : Fin n) : (rationalScore δ D S Δ s u v:ℝ)=branchScore D S (Δ:ℝ) s.real u v :=
    congrFun (congrFun he u) v
  simp only [hev] at hv
  exact hv.le.trans hvalue
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
noncomputable def run (d : ℕ) (x : List Bool) : List Bool :=
  if BinaryBranchCheck.run (extractPrefix x) then
    if best d (extractPrefix x)=[] then field 3 (extractPrefix x) else BinaryBranchProgram.run d x
  else field 3 (extractPrefix x)
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (extractPrefix_computes.comp BinaryBranchCheck.run_computes).cond
      (((extractPrefix_computes.comp (best_computes d)).comp isEmpty_computes).cond
        (extractPrefix_computes.comp (field_computes 3)) (BinaryBranchProgram.run_computes d))
      (extractPrefix_computes.comp (field_computes 3))
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (colors : Fin n→Fin 3) (label : Fin n→Fin m) (q c : ℕ) (r0 y0 : Fin n)
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) : Finset (Fin n) := by
  classical
  exact if hr : BinaryBranchCheck.Ready δ F S s colors q c m then
    match hb : BlueDP.best (BlueDP.block ((S\s.deleted).filter (fun i=>colors i=2)) F label (rationalScore δ D S Δ s)) c Finset.univ with
    | none=>S
    | some (v,xs)=>
      let P:=BlueDP.makePlan _ _ _ _ _ r0 y0 v xs hb
      result δ D F S Δ s colors hr.2.1 P.sel P.dst q bits
  else S
section Output
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (q c : ℕ) (r0 y0 : Fin n)
    (hr : BinaryBranchCheck.Ready δ F S s colors q c m)
local notation "blue" => Finset.filter (fun i=>colors i=2) (S\s.deleted)
local notation "score" => rationalScore δ D S Δ s
include hr in
lemma output_none (hb : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=none) (bits) :
    output δ D F S Δ s colors label q c r0 y0 bits=S := by
  classical
  unfold output
  rw [dite_eq_left hr]
  split
  · rfl
  · rename_i v xs he
    rw [hb] at he
    contradiction
lemma output_some (v : ℚ) (xs : List (BlueDP.Atom (Fin m) (Fin n) (Fin n)))
    (hb : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs)) (bits) :
    output δ D F S Δ s colors label q c r0 y0 bits=
      result δ D F S Δ s colors hr.2.1 (BlueDP.makePlan blue F label score c r0 y0 v xs hb).sel
        (BlueDP.makePlan blue F label score c r0 y0 v xs hb).dst q bits := by
  classical
  unfold output
  rw [dite_eq_left hr]
  split
  · rename_i he
    rw [hb] at he
    contradiction
  · rename_i v' xs' he
    have hh : (v',xs')=(v,xs) := Option.some.inj (he.symm.trans hb)
    cases hh
    rfl
end Output
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (q c : ℕ) (extra : List Bool) (d : ℕ)
local notation "data" => BinaryBranchContext.pack δ D F S Δ s colors label q c extra
local notation "blue" => Finset.filter (fun i=>colors i=2) (S\RationalSampling.State.deleted s)
local notation "score" => rationalScore δ D S Δ s
lemma best_pack (hcap : 2^m*(2*(BinaryFinSet.encode (Finset.univ : Finset (Fin m))).length+2)≤
      (pairBits (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c,
        BinaryFinSet.encode (Finset.univ : Finset (Fin m)))).length.succ^d) :
    best d data=BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc (fun i : Fin n=>i.val.bits)))
      (BlueDP.best (BlueDP.block blue F label score) c Finset.univ) := by
  rw [best,bluePack_pack]
  exact BinaryBlueProgram.run_pack d extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c (by simpa using hcap)
lemma run_pack (r0 y0 : Fin n)
    (hcap : 2^m*(2*(BinaryFinSet.encode (Finset.univ : Finset (Fin m))).length+2)≤
      (pairBits (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c,
        BinaryFinSet.encode (Finset.univ : Finset (Fin m)))).length.succ^d)
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) :
    run d (pairBits (data,BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length
      (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
      BinaryFinSet.encode (output δ D F S Δ s colors label q c r0 y0 bits) := by
  classical
  rw [run,extractPrefix_pairBits,BinaryBranchCheck.run_pack]
  simp only [decide_eq_true_eq]
  by_cases hr : BinaryBranchCheck.Ready δ F S s colors q c m
  · rw [ite_eq_left hr,best_pack δ D F S Δ s colors label q c extra d hcap]
    have hx : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=none ∨
        ∃ v xs,BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs) := by
      cases ht : BlueDP.best (BlueDP.block blue F label score) c Finset.univ with
      | none=>exact Or.inl rfl
      | some x=>exact Or.inr ⟨x.1,x.2,rfl⟩
    rcases hx with hb | ⟨v,xs,hb⟩
    ·
      rw [output_none δ D F S Δ s colors label q c r0 y0 hr hb]
      simp only [hb,BinaryBlueChoice.encode,ite_true]
      simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
    ·
      have hn : BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc (fun i : Fin n=>i.val.bits))) (some (v,xs))≠[] := by
        simp [BinaryBlueChoice.encode,WordList.encode,WordList.cons,pairBits]
      rw [output_some δ D F S Δ s colors label q c r0 y0 hr v xs hb]
      simp only [hb,ite_eq_right hn]
      have hp:=plan_pack δ D F S Δ s colors label q c extra d r0 y0 v xs hb hcap
      exact BinaryBranchProgram.run_pack δ D F S Δ s colors label q c extra hr.2.1 d _ _ hp bits
  · rw [ite_eq_right hr]
    rw [output,dite_eq_right hr]
    simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
end Correct
variable [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (label : Fin n→Fin m) (q c : ℕ) (r0 y0 : Fin n) (bits) :
    output δ D F S Δ s colors label q c r0 y0 bits⊆F ∧
      (output δ D F S Δ s colors label q c r0 y0 bits).card=S.card ∧
      (output δ D F S Δ s colors label q c r0 y0 bits).Nonempty := by
  classical
  unfold output
  split_ifs with hr
  · split
    · exact ⟨hSF,rfl,hS⟩
    · rename_i v xs hb
      let P:=BlueDP.makePlan _ _ _ _ _ r0 y0 v xs hb
      have hradius (i : Fin s.leaves.length) : 0≤ s.radius i := by
        change (0:ℝ)≤(s.leaves[i.val].2:ℝ)
        exact_mod_cast hr.2.2.1 _ (List.getElem_mem i.isLt)
      exact (result_guarantee δ hδ D F S hSF hS Δ hΔ hbound s hr.1 colors hr.2.1 hradius P.sel P.dst c q
        P.selected_injective (fun j=>(P.selection j).1) (fun j=>(P.selection j).2.2) P.destination_count hr.2.2.2.2 hr.2.2.2.1).1 bits
  · exact ⟨hSF,rfl,hS⟩
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
