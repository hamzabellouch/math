import OAI.Computability.PerfectCompleteness.Construction.WholeCutLocalityLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerKeyLocalityLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def Tape (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → Type
  | _, m, .refl _, slots, clean =>
      (i : {i : Fin (branch m) // ¬ clean i}) →
        CutChildGrouping.Child (C := Fin (rows (m + 1))) slots rows i.val
  | n + 1, _, .step i p, slots, clean =>
      (BucketSampler.Direction (rows (n + 1)) →
        CutSamplerReplay.Tape F2 repeats (.step i p) (LeafDomain slots) clean) ×
      (Tape rows repeats p (childSlots slots i) clean ×
        ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))

def erase (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → WholeCutSampler.Tape rows repeats p slots →
        Tape rows repeats p slots clean
  | _, _, .refl _, _, _, tape => fun i => tape i.val
  | _, _, .step i p, slots, clean, tape =>
      (fun bucket => CutSamplerReplay.erase F2 repeats (.step i p)
        (LeafDomain slots) clean (tape.1 bucket),
        erase rows repeats p (childSlots slots i) clean tape.2.1, tape.2.2)

def evaluate (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → Tape rows repeats p slots clean →
        Domain slots → (node : Nodes branch n) → Block rows node
  | _, m, .refl _, slots, clean, tape, x, .inl _, row =>
      ∑ i : {i : Fin (branch m) // ¬ clean i},
        ((tape i).1 row).val (restrictChild slots i.val x)
  | _, _, .refl _, slots, clean, tape, x, .inr (i, node), row =>
      if hi : ¬ clean i then
        ((tape ⟨i, hi⟩).2 node row).val
          (restrictNode (childSlots slots i) node (restrictChild slots i x))
      else 0
  | n + 1, _, .step i p, slots, clean, tape, x, .inl _, row =>
      ∑ bucket : BucketSampler.Direction (rows (n + 1)), bucket.val row *
        CutSamplerReplay.evaluate F2 repeats (.step i p) (LeafDomain slots)
          clean (tape.1 bucket) x
  | _, _, .step i p, slots, clean, tape, x, .inr (j, node), row =>
      if hji : j = i then
        evaluate rows repeats p (childSlots slots i) clean tape.2.1
          (restrictChild slots i x) node row
      else
        ((tape.2.2 ⟨j, hji⟩) node row).val
          (restrictNode (childSlots slots j) node (restrictChild slots j x))

theorem evaluate_refl_root (rows repeats : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.refl (m + 1)) slots clean) (x : Domain slots)
    (row : Fin (rows (m + 1))) :
    evaluate rows repeats (.refl (m + 1)) slots clean tape x (.inl ()) row =
      ∑ i : {i : Fin (branch m) // ¬ clean i},
        ((tape i).1 row).val (restrictChild slots i.val x) := rfl

theorem evaluate_refl_child (rows repeats : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.refl (m + 1)) slots clean) (x : Domain slots)
    (i : Fin (branch m)) (node : Nodes branch m) (row : Fin (rows (Nodes.height node))) :
    evaluate rows repeats (.refl (m + 1)) slots clean tape x (.inr (i, node)) row =
      if hi : ¬ clean i then
        ((tape ⟨i, hi⟩).2 node row).val
          (restrictNode (childSlots slots i) node (restrictChild slots i x))
      else 0 := rfl

theorem evaluate_step_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean) (x : Domain slots)
    (row : Fin (rows (n + 1))) :
    evaluate rows repeats (.step i p) slots clean tape x (.inl ()) row =
      ∑ bucket : BucketSampler.Direction (rows (n + 1)), bucket.val row *
        CutSamplerReplay.evaluate F2 repeats (.step i p) (LeafDomain slots)
          clean (tape.1 bucket) x := rfl

theorem evaluate_step_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean) (x : Domain slots)
    (node : Nodes branch n) (row : Fin (rows (Nodes.height node))) :
    evaluate rows repeats (.step i p) slots clean tape x (.inr (i, node)) row =
      evaluate rows repeats p (childSlots slots i) clean tape.2.1
        (restrictChild slots i x) node row := by
  simp only [evaluate]
  exact dite_eq_left True.intro

theorem evaluate_step_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean) (x : Domain slots)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n)
    (row : Fin (rows (Nodes.height node))) :
    evaluate rows repeats (.step i p) slots clean tape x (.inr (j.val, node)) row =
      ((tape.2.2 j) node row).val
        (restrictNode (childSlots slots j.val) node (restrictChild slots j.val x)) := by
  simp only [evaluate, dite_eq_right j.property]

theorem evaluate_erase (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (tape : WholeCutSampler.Tape rows repeats p slots),
      WholeCutZero.ZeroAtClean rows repeats p slots clean tape →
      ∀ x : Domain slots,
        evaluate rows repeats p slots clean (erase rows repeats p slots clean tape) x =
          joint (WholeCutSampler.evaluate rows repeats p slots tape) x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots clean tape hzero x
          funext node row
          rcases node with u | ⟨i, node⟩
          · cases u
            let scalarTape : CutSamplerRefinement.Tape F2 repeats (.refl (n + 1))
                (LeafDomain slots) := fun _ i => (tape i).1 row
            have hz : CutSamplerLocality.ZeroAtClean F2 repeats (.refl (n + 1))
                (LeafDomain slots) clean scalarTape :=
              fun i hi => (hzero i hi).1 row
            exact CutSamplerReplay.evaluate_erase F2 repeats (.refl (n + 1))
              (LeafDomain slots) clean scalarTape hz x
          · refine (evaluate_refl_child rows repeats slots clean
              (erase rows repeats (.refl (n + 1)) slots clean tape) x i node row).trans ?_
            change (if hi : ¬ clean i then
                ((tape i).2 node row).val
                  (restrictNode (childSlots slots i) node (restrictChild slots i x))
                else 0) =
              ((tape i).2 node row).val
                (restrictNode (childSlots slots i) node (restrictChild slots i x))
            by_cases hi : clean i
            · rw [dite_eq_right (not_not_intro hi), (hzero i hi).2 node row]
              rfl
            · rw [dite_eq_left hi]
      | step i p =>
          intro slots clean tape hzero x
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            refine (evaluate_step_root rows repeats i p slots clean
              (erase rows repeats (.step i p) slots clean tape) x row).trans ?_
            change (∑ bucket : BucketSampler.Direction (rows (n + 1)), bucket.val row *
                CutSamplerReplay.evaluate F2 repeats (.step i p) (LeafDomain slots) clean
                  (CutSamplerReplay.erase F2 repeats (.step i p) (LeafDomain slots)
                    clean (tape.1 bucket)) x) =
              (WholeCutSampler.evaluate rows repeats (.step i p) slots tape (.inl ()) row).val x
            have heval := BucketSampler.evaluate_apply (rows (n + 1))
              (space F2 branch (n + 1) (LeafDomain slots))
              (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain slots))
              tape.1 row x
            refine Eq.trans ?_ heval.symm
            refine Finset.sum_congr (ι := BucketSampler.Direction (rows (n + 1))) ?_ ?_
            · ext bucket
              simp only [Finset.mem_univ]
            · intro bucket _
              exact congrArg (fun z : F2 => bucket.val row * z)
                (CutSamplerReplay.evaluate_erase F2 repeats (.step i p)
                  (LeafDomain slots) clean (tape.1 bucket) (hzero.1 bucket) x)
          · by_cases hji : j = i
            · subst j
              refine (evaluate_step_selected rows repeats i p slots clean
                (erase rows repeats (.step i p) slots clean tape) x node row).trans ?_
              exact (congrFun (congrFun
                (ih p (childSlots slots i) clean tape.2.1 hzero.2
                  (restrictChild slots i x)) node) row).trans
                (congrArg
                  (fun block : Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots i) node) =>
                    (block row).val
                      (restrictNode (childSlots slots i) node (restrictChild slots i x)))
                  (WholeCutLocality.evaluate_selected rows repeats i p slots tape node)).symm
            · refine (evaluate_step_ordinary rows repeats i p slots clean
                (erase rows repeats (.step i p) slots clean tape) x ⟨j, hji⟩ node row).trans ?_
              exact (congrArg
                (fun block : Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots j) node) =>
                  (block row).val
                    (restrictNode (childSlots slots j) node (restrictChild slots j x)))
                (WholeCutLocality.evaluate_ordinary rows repeats i p slots tape ⟨j, hji⟩ node)).symm

theorem evaluate_erase_of_grouped_zero (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape) (x : Domain slots) :
    evaluate rows repeats p slots clean (erase rows repeats p slots clean tape) x =
      joint (WholeCutSampler.evaluate rows repeats p slots tape) x :=
  evaluate_erase rows repeats p slots clean tape
    ((WholeCutZero.grouped_iff rows repeats p slots clean tape).mp hzero) x

def fullQuery (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : Tape rows repeats p slots clean)
    (x : Domain slots) : Output branch n rows :=
  (evaluate rows repeats p slots clean tape x, PUnit.unit)

theorem fullQuery_erase_of_grouped_zero (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape) (x : Domain slots) :
    fullQuery rows repeats p slots clean (erase rows repeats p slots clean tape) x =
      fullJoint (WholeCutSampler.evaluate rows repeats p slots tape) x :=
  Prod.ext (evaluate_erase_of_grouped_zero rows repeats p slots clean tape hzero x) rfl

end
end PerfectCompleteness.WholeCutReplay

end

section

namespace PerfectCompleteness.WholeCutReplayGrouping

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev RetainedChildren (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (clean : Fin (branch m) → Prop) :=
  (i : {i : Fin (branch m) // ¬ clean i}) →
    CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p slots) rows i.val

def assemble (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → WholeCutGrouping.Exterior rows repeats p slots →
        RetainedChildren rows repeats p slots clean → WholeCutReplay.Tape rows repeats p slots clean
  | _, _, .refl _, _, _, _, children => children
  | _, _, .step i p, slots, clean, exterior, children =>
      (fun bucket => CutSamplerReplayGrouping.assemble F2 repeats (.step i p)
        (LeafDomain slots) clean (exterior.1 bucket)
        (fun terminal child => (children child).1 (.inl (bucket, terminal))),
        assemble rows repeats p (childSlots slots i) clean exterior.2.1
          (fun child => (fun q => (children child).1 (.inr q), (children child).2)),
        exterior.2.2)

theorem assemble_splitTape (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots),
      assemble rows repeats p slots clean
          (WholeCutGrouping.splitTape rows repeats p slots tape).1
          (fun child => (WholeCutGrouping.splitTape rows repeats p slots tape).2 child.val) =
        WholeCutReplay.erase rows repeats p slots clean tape := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots clean tape
          rfl
      | step i p =>
          intro slots clean tape
          apply Prod.ext
          · funext bucket
            exact CutSamplerReplayGrouping.assemble_splitTape F2 repeats (.step i p)
              (LeafDomain slots) clean (tape.1 bucket)
          · apply Prod.ext
            · exact ih p (childSlots slots i) clean tape.2.1
            · rfl

theorem evaluate_assemble_splitTape (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape) (x : Domain slots) :
    WholeCutReplay.evaluate rows repeats p slots clean
        (assemble rows repeats p slots clean
          (WholeCutGrouping.splitTape rows repeats p slots tape).1
          (fun child => (WholeCutGrouping.splitTape rows repeats p slots tape).2 child.val)) x =
      joint (WholeCutSampler.evaluate rows repeats p slots tape) x := by
  rw [assemble_splitTape]
  exact WholeCutReplay.evaluate_erase_of_grouped_zero rows repeats p slots clean tape hzero x

theorem fullQuery_assemble_splitTape (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape) (x : Domain slots) :
    WholeCutReplay.fullQuery rows repeats p slots clean
        (assemble rows repeats p slots clean
          (WholeCutGrouping.splitTape rows repeats p slots tape).1
          (fun child => (WholeCutGrouping.splitTape rows repeats p slots tape).2 child.val)) x =
      fullJoint (WholeCutSampler.evaluate rows repeats p slots tape) x :=
  Prod.ext (evaluate_assemble_splitTape rows repeats p slots clean tape hzero x) rfl

end
end PerfectCompleteness.WholeCutReplayGrouping

end

section

namespace PerfectCompleteness.CutSamplerReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def retainedSum (𝕜 : Type w) [Field 𝕜]
    (A : Slots branch (m + 1) → Type u) (clean : Fin (branch m) → Prop)
    (tape : (i : {i : Fin (branch m) // ¬ clean i}) →
      squareSpace (space 𝕜 branch m (childFamily A i.val))) :
    space 𝕜 branch (m + 1) A :=
  ⟨∑ i : {i : Fin (branch m) // ¬ clean i},
      pullback 𝕜 (childRestriction A i.val) (tape i).val, by
    apply (space 𝕜 branch (m + 1) A).sum_mem
    intro i _
    exact child_square_le_space A i.val
      (Submodule.mem_map_of_mem (tape i).property)⟩

@[simp] theorem retainedSum_apply (𝕜 : Type w) [Field 𝕜]
    (A : Slots branch (m + 1) → Type u) (clean : Fin (branch m) → Prop)
    (tape : (i : {i : Fin (branch m) // ¬ clean i}) →
      squareSpace (space 𝕜 branch m (childFamily A i.val))) (x : Assignment A) :
    (retainedSum 𝕜 A clean tape).val x =
      ∑ i : {i : Fin (branch m) // ¬ clean i},
        (tape i).val (childRestriction A i.val x) := by
  simp only [retainedSum, Finset.sum_apply, PointwiseSpaces.pullback_apply]

def evaluateSpace (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) → Tape 𝕜 repeats p A clean →
        space 𝕜 branch n A
  | _, _, .refl _, A, clean, tape => retainedSum 𝕜 A clean tape
  | n + 1, _, .step i p, A, clean, tape =>
      RecursiveSampler.combine 𝕜 A i (repeats (n + 1)) tape.1
        (fun h => evaluateSpace 𝕜 repeats p (childFamily A i) clean (tape.2 (h, false)))
        (fun h => evaluateSpace 𝕜 repeats p (childFamily A i) clean (tape.2 (h, true)))

theorem evaluateSpace_apply (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (tape : Tape 𝕜 repeats p A clean) (x : Assignment A),
      (evaluateSpace 𝕜 repeats p A clean tape).val x =
        evaluate 𝕜 repeats p A clean tape x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean tape x
          exact retainedSum_apply 𝕜 A clean tape x
      | step i p =>
          intro A clean tape x
          rw [evaluateSpace, evaluate_step]
          simp only [RecursiveSampler.combine, RecursiveSampler.combineFunction,
            Finset.sum_apply, Pi.add_apply, Pi.mul_apply, PointwiseSpaces.pullback_apply]
          apply congrArg (fun z =>
            (∑ j : OffPath i, (tape.1 j).val (childRestriction A j.val x)) + z)
          apply Finset.sum_congr rfl
          intro h _
          rw [ih p (childFamily A i) clean (tape.2 (h, false)),
            ih p (childFamily A i) clean (tape.2 (h, true))]

theorem evaluateSpace_val (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
    (tape : Tape 𝕜 repeats p A clean) :
    (evaluateSpace 𝕜 repeats p A clean tape).val = evaluate 𝕜 repeats p A clean tape :=
  funext (evaluateSpace_apply 𝕜 repeats p A clean tape)

theorem evaluateSpace_erase (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats p A)
    (hzero : CutSamplerLocality.ZeroAtClean 𝕜 repeats p A clean tape) :
    evaluateSpace 𝕜 repeats p A clean (erase 𝕜 repeats p A clean tape) =
      CutSamplerRefinement.evaluate 𝕜 repeats p A tape := by
  apply Subtype.ext
  funext x
  rw [evaluateSpace_apply]
  exact evaluate_erase 𝕜 repeats p A clean tape hzero x

end
end PerfectCompleteness.CutSamplerReplay

namespace PerfectCompleteness.HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem joint_injective
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :
    Function.Injective (joint (slots := slots) (rows := rows)) := by
  intro a b hab
  funext node row
  apply Subtype.ext
  funext x
  obtain ⟨global, rfl⟩ := restrictNode_surjective slots node x
  exact congrFun (congrFun (congrFun hab global) node) row

end
end PerfectCompleteness.HierarchicalArrays

namespace PerfectCompleteness.WholeCutReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def evaluateArrays (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → Tape rows repeats p slots clean → Arrays slots rows
  | _, m, .refl _, slots, clean, tape =>
      WholeArraySampler.assemble slots rows
        (fun row => CutSamplerReplay.evaluateSpace F2 repeats (.refl (m + 1))
          (LeafDomain slots) clean (fun i => (tape i).1 row))
        (fun i => if hi : ¬ clean i then (tape ⟨i, hi⟩).2 else fun _ _ => 0)
  | n + 1, _, .step i p, slots, clean, tape =>
      WholeArraySampler.assemble slots rows
        (BucketSampler.evaluate (rows (n + 1))
          (CutSamplerReplay.evaluateSpace F2 repeats (.step i p) (LeafDomain slots) clean) tape.1)
        (WholeArraySampler.childrenAt slots rows i
          (evaluateArrays rows repeats p (childSlots slots i) clean tape.2.1) tape.2.2)

def bucketSpace (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean)
    (bucket : BucketSampler.Direction (rows (n + 1))) : H slots :=
  CutSamplerReplay.evaluateSpace F2 repeats (.step i p) (LeafDomain slots) clean
    (tape.1 bucket)

theorem bucketSpace_apply (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean)
    (bucket : BucketSampler.Direction (rows (n + 1))) (x : Domain slots) :
    (bucketSpace rows repeats i p slots clean tape bucket).val x =
      CutSamplerReplay.evaluate F2 repeats (.step i p) (LeafDomain slots) clean
        (tape.1 bucket) x :=
  CutSamplerReplay.evaluateSpace_apply F2 repeats (.step i p) (LeafDomain slots) clean
    (tape.1 bucket) x

theorem evaluateArrays_step_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean) :
    evaluateArrays rows repeats (.step i p) slots clean tape (.inl ()) =
      BucketSampler.evaluate (rows (n + 1))
        (CutSamplerReplay.evaluateSpace F2 repeats (.step i p) (LeafDomain slots) clean)
        tape.1 := rfl

theorem evaluateArrays_step_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean) (node : Nodes branch n) :
    evaluateArrays rows repeats (.step i p) slots clean tape (.inr (i, node)) =
      evaluateArrays rows repeats p (childSlots slots i) clean tape.2.1 node := by
  exact congrFun (WholeArraySampler.childrenAt_selected slots rows i
    (evaluateArrays rows repeats p (childSlots slots i) clean tape.2.1) tape.2.2) node

theorem evaluateArrays_step_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    evaluateArrays rows repeats (.step i p) slots clean tape (.inr (j.val, node)) =
      tape.2.2 j node := by
  exact congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
    (evaluateArrays rows repeats p (childSlots slots i) clean tape.2.1) tape.2.2 j) node

theorem joint_evaluateArrays_apply (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop) (tape : Tape rows repeats p slots clean)
      (x : Domain slots),
      joint (evaluateArrays rows repeats p slots clean tape) x =
        evaluate rows repeats p slots clean tape x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots clean tape x
          funext node row
          rcases node with u | ⟨i, node⟩
          · cases u
            exact CutSamplerReplay.evaluateSpace_apply F2 repeats (.refl (n + 1))
              (LeafDomain slots) clean (fun i => (tape i).1 row) x
          · change
              (((if hi : ¬ clean i then (tape ⟨i, hi⟩).2 else fun _ _ => 0) :
                Arrays (childSlots slots i) rows) node row).val
                  (restrictNode (childSlots slots i) node (restrictChild slots i x)) =
                (if hi : ¬ clean i then
                  ((tape ⟨i, hi⟩).2 node row).val
                    (restrictNode (childSlots slots i) node (restrictChild slots i x))
                else 0)
            by_cases hi : ¬ clean i
            · simp only [dite_eq_left hi]
            · simp only [dite_eq_right hi]
              rfl
      | step i p =>
          intro slots clean tape x
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            change (BucketSampler.evaluate (rows (n + 1))
                (CutSamplerReplay.evaluateSpace F2 repeats (.step i p) (LeafDomain slots) clean)
                tape.1 row).val x =
              ∑ bucket : BucketSampler.Direction (rows (n + 1)), bucket.val row *
                CutSamplerReplay.evaluate F2 repeats (.step i p) (LeafDomain slots)
                  clean (tape.1 bucket) x
            have heval := BucketSampler.evaluate_apply (rows (n + 1))
              (space F2 branch (n + 1) (LeafDomain slots))
              (CutSamplerReplay.evaluateSpace F2 repeats (.step i p) (LeafDomain slots) clean)
              tape.1 row x
            refine heval.trans ?_
            refine Finset.sum_congr (ι := BucketSampler.Direction (rows (n + 1))) ?_ ?_
            · ext bucket
              simp only [Finset.mem_univ]
            · intro bucket _
              exact congrArg (fun z : F2 => bucket.val row * z)
                (CutSamplerReplay.evaluateSpace_apply F2 repeats (.step i p)
                  (LeafDomain slots) clean (tape.1 bucket) x)
          · by_cases hji : j = i
            · subst j
              exact (congrArg
                (fun block : Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots i) node) =>
                  (block row).val
                    (restrictNode (childSlots slots i) node (restrictChild slots i x)))
                (evaluateArrays_step_selected rows repeats i p slots clean tape node)).trans
                  ((congrFun (congrFun
                    (ih p (childSlots slots i) clean tape.2.1 (restrictChild slots i x)) node) row).trans
                    (evaluate_step_selected rows repeats i p slots clean tape x node row).symm)
            · exact (congrArg
                (fun block : Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots j) node) =>
                  (block row).val
                    (restrictNode (childSlots slots j) node (restrictChild slots j x)))
                (evaluateArrays_step_ordinary rows repeats i p slots clean tape ⟨j, hji⟩ node)).trans
                  (evaluate_step_ordinary rows repeats i p slots clean tape x ⟨j, hji⟩ node row).symm

theorem joint_evaluateArrays (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : Tape rows repeats p slots clean) :
    joint (evaluateArrays rows repeats p slots clean tape) =
      evaluate rows repeats p slots clean tape :=
  funext (joint_evaluateArrays_apply rows repeats p slots clean tape)

theorem fullJoint_evaluateArrays (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : Tape rows repeats p slots clean) :
    fullJoint (evaluateArrays rows repeats p slots clean tape) =
      fullQuery rows repeats p slots clean tape := by
  funext x
  exact Prod.ext (joint_evaluateArrays_apply rows repeats p slots clean tape x) rfl

theorem evaluateArrays_erase (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.ZeroAtClean rows repeats p slots clean tape) :
    evaluateArrays rows repeats p slots clean (erase rows repeats p slots clean tape) =
      WholeCutSampler.evaluate rows repeats p slots tape := by
  apply HierarchicalArrays.joint_injective slots rows
  funext x
  rw [joint_evaluateArrays_apply]
  exact evaluate_erase rows repeats p slots clean tape hzero x

theorem evaluateArrays_erase_of_grouped_zero (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape) :
    evaluateArrays rows repeats p slots clean (erase rows repeats p slots clean tape) =
      WholeCutSampler.evaluate rows repeats p slots tape :=
  evaluateArrays_erase rows repeats p slots clean tape
    ((WholeCutZero.grouped_iff rows repeats p slots clean tape).mp hzero)

theorem bucketSpace_erase (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots)
    (hzero : WholeCutZero.ZeroAtClean rows repeats (.step i p) slots clean tape)
    (bucket : BucketSampler.Direction (rows (n + 1))) :
    bucketSpace rows repeats i p slots clean
        (erase rows repeats (.step i p) slots clean tape) bucket =
      CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain slots) (tape.1 bucket) :=
  CutSamplerReplay.evaluateSpace_erase F2 repeats (.step i p) (LeafDomain slots) clean
    (tape.1 bucket) (hzero.1 bucket)

end
end PerfectCompleteness.WholeCutReplay

namespace PerfectCompleteness.WholeCutReplayGrouping

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem evaluateArrays_assemble_splitTape (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape) :
    WholeCutReplay.evaluateArrays rows repeats p slots clean
        (assemble rows repeats p slots clean
          (WholeCutGrouping.splitTape rows repeats p slots tape).1
          (fun child => (WholeCutGrouping.splitTape rows repeats p slots tape).2 child.val)) =
      WholeCutSampler.evaluate rows repeats p slots tape := by
  rw [assemble_splitTape]
  exact WholeCutReplay.evaluateArrays_erase_of_grouped_zero rows repeats p slots clean tape hzero

end
end PerfectCompleteness.WholeCutReplayGrouping

end

section

namespace PerfectCompleteness.WholeCutReplayTransport

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open CutSamplerKeyLocality
open scoped BigOperators Classical

noncomputable section

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n m t : Nat}

def arraysTransport (rows : Nat → Nat)
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (e : ∀ s, LeafDomain slots s ≃ LeafDomain target s)
    (arrays : Arrays slots rows) : Arrays target rows :=
  fun node row => (RecursiveSpaceEquiv.spaceEquiv (𝕜 := F2)
    (fun s => e ((Nodes.path node).slotEmbedding s))).symm (arrays node row)

theorem joint_arraysTransport (rows : Nat → Nat)
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (e : ∀ s, LeafDomain slots s ≃ LeafDomain target s)
    (arrays : Arrays slots rows) (x : Domain slots) (y : Domain target)
    (hagree : ∀ s, e s (x s) = y s) :
    joint (arraysTransport rows slots target e arrays) y = joint arrays x := by
  funext node row
  change (arrays node row).val
      (project (fun s => (e ((Nodes.path node).slotEmbedding s)).symm)
        (restrictNode target node y)) =
    (arrays node row).val (restrictNode slots node x)
  apply congrArg (arrays node row).val
  funext s
  exact (congrArg (e ((Nodes.path node).slotEmbedding s)).symm
    (hagree ((Nodes.path node).slotEmbedding s))).symm.trans
      ((e ((Nodes.path node).slotEmbedding s)).symm_apply_apply
        (x ((Nodes.path node).slotEmbedding s)))

def transport (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) →
    (clean : Fin (branch m) → Prop) →
    (∀ s, keptLeaf p clean s → LeafDomain slots s ≃ LeafDomain target s) →
    WholeCutReplay.Tape rows repeats p slots clean →
      WholeCutReplay.Tape rows repeats p target clean
  | _, _, .refl _, slots, target, _, e, tape =>
      fun i =>
        (fun q => (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
          (fun s => e (i.val, s) i.property)).symm ((tape i).1 q),
          arraysTransport rows (childSlots slots i.val) (childSlots target i.val)
            (fun s => e (i.val, s) i.property) (tape i).2)
  | _, _, .step i p, slots, target, clean, e, tape =>
      (fun v => CutSamplerReplayTransport.transport F2 repeats (.step i p)
        (LeafDomain slots) (LeafDomain target) clean e (tape.1 v),
        transport rows repeats p (childSlots slots i) (childSlots target i) clean
          (fun s hs => e (i, s) (Or.inr hs)) tape.2.1,
        fun j => arraysTransport rows (childSlots slots j.val) (childSlots target j.val)
          (fun s => e (j.val, s) (Or.inl j.property)) (tape.2.2 j))

theorem evaluate_transport (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots target : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (e : ∀ s, keptLeaf p clean s → LeafDomain slots s ≃ LeafDomain target s)
      (tape : WholeCutReplay.Tape rows repeats p slots clean)
      (x : Domain slots) (y : Domain target),
      (∀ s hs, e s hs (x s) = y s) →
      WholeCutReplay.evaluate rows repeats p target clean
          (transport rows repeats p slots target clean e tape) y =
        WholeCutReplay.evaluate rows repeats p slots clean tape x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots target clean e tape x y hagree
          funext node row
          rcases node with u | ⟨i, node⟩
          · cases u
            refine (WholeCutReplay.evaluate_refl_root rows repeats target clean
              (transport rows repeats (.refl (n + 1)) slots target clean e tape) y row).trans ?_
            refine Eq.trans ?_ (WholeCutReplay.evaluate_refl_root
              rows repeats slots clean tape x row).symm
            apply Finset.sum_congr rfl
            intro i _
            exact CutSamplerReplayTransport.squareEquiv_symm_eval_of_agree F2
              (fun s => e (i.val, s) i.property) ((tape i).1 row)
              (restrictChild slots i.val x) (restrictChild target i.val y)
              (fun s => hagree (i.val, s) i.property)
          · refine (WholeCutReplay.evaluate_refl_child rows repeats target clean
              (transport rows repeats (.refl (n + 1)) slots target clean e tape)
              y i node row).trans ?_
            refine Eq.trans ?_ (WholeCutReplay.evaluate_refl_child
              rows repeats slots clean tape x i node row).symm
            by_cases hi : ¬ clean i
            · simp only [dite_eq_left hi]
              exact congrFun (congrFun
                (joint_arraysTransport rows (childSlots slots i) (childSlots target i)
                  (fun s => e (i, s) hi) (tape ⟨i, hi⟩).2
                  (restrictChild slots i x) (restrictChild target i y)
                  (fun s => hagree (i, s) hi)) node) row
            · simp only [dite_eq_right hi]
      | step i p =>
          intro slots target clean e tape x y hagree
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            refine (WholeCutReplay.evaluate_step_root rows repeats i p target clean
              (transport rows repeats (.step i p) slots target clean e tape) y row).trans ?_
            refine Eq.trans ?_ (WholeCutReplay.evaluate_step_root
              rows repeats i p slots clean tape x row).symm
            apply Finset.sum_congr rfl
            intro bucket _
            apply congrArg (fun z : F2 => bucket.val row * z)
            exact CutSamplerReplayTransport.evaluate_transport F2 repeats (.step i p)
              (LeafDomain slots) (LeafDomain target) clean e (tape.1 bucket) x y hagree
          · by_cases hji : j = i
            · subst j
              refine (WholeCutReplay.evaluate_step_selected rows repeats i p target clean
                (transport rows repeats (.step i p) slots target clean e tape)
                y node row).trans ?_
              refine Eq.trans ?_ (WholeCutReplay.evaluate_step_selected
                rows repeats i p slots clean tape x node row).symm
              exact congrFun (congrFun
                (ih p (childSlots slots i) (childSlots target i) clean
                  (fun s hs => e (i, s) (Or.inr hs)) tape.2.1
                  (restrictChild slots i x) (restrictChild target i y)
                  (fun s hs => hagree (i, s) (Or.inr hs))) node) row
            · rw [WholeCutReplay.evaluate_step_ordinary rows repeats i p target clean
                (transport rows repeats (.step i p) slots target clean e tape)
                y ⟨j, hji⟩ node row,
                WholeCutReplay.evaluate_step_ordinary rows repeats i p slots clean tape
                  x ⟨j, hji⟩ node row]
              exact congrFun (congrFun
                (joint_arraysTransport rows (childSlots slots j) (childSlots target j)
                  (fun s => e (j, s) (Or.inl hji)) (tape.2.2 ⟨j, hji⟩)
                  (restrictChild slots j x) (restrictChild target j y)
                  (fun s => hagree (j, s) (Or.inl hji))) node) row

theorem fullQuery_transport (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (e : ∀ s, keptLeaf p clean s → LeafDomain slots s ≃ LeafDomain target s)
    (tape : WholeCutReplay.Tape rows repeats p slots clean)
    (x : Domain slots) (y : Domain target)
    (hagree : ∀ s hs, e s hs (x s) = y s) :
    WholeCutReplay.fullQuery rows repeats p target clean
        (transport rows repeats p slots target clean e tape) y =
      WholeCutReplay.fullQuery rows repeats p slots clean tape x :=
  Prod.ext (evaluate_transport rows repeats p slots target clean e tape x y hagree) rfl

end
end PerfectCompleteness.WholeCutReplayTransport

end

end OAI
