import OAI.Computability.PerfectCompleteness.Algebra.BucketMatrixResampling
import OAI.Computability.PerfectCompleteness.Foundations.OriginalWholeCut
import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayInteriorExteriorLemmas

namespace OAI

section

namespace PerfectCompleteness.OriginalCutBucketReplacement

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut OriginalWholeCutTape
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def ownValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (values : Values rows repeats p slots) :
    BucketSampler.Direction (rows (m + 1)) → H (cutSlots p slots) :=
  fun a => values (OriginalCutCalls.ownBucket rows repeats p a)

def replaceValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (values : Values rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots)) :
    Values rows repeats p slots :=
  Function.update values (OriginalCutCalls.ownBucket rows repeats p a) fresh

theorem ownValues_replaceValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (values : Values rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots)) :
    ownValues rows repeats p slots (replaceValues rows repeats p slots values a fresh) =
      Function.update (ownValues rows repeats p slots values) a fresh :=
  Function.update_comp_eq_of_injective' values
    (OriginalCutCalls.ownBucket_injective rows repeats p) a fresh

theorem replaceValues_rootCalls (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (values : Values rows repeats (.step i p) slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (fresh : H (cutSlots (.step i p) slots)) :
    (fun direction terminal => replaceValues rows repeats (.step i p) slots values a fresh
        (.inl (direction, terminal))) =
      (fun direction terminal => values (.inl (direction, terminal))) := by
  funext direction terminal
  exact Function.update_of_ne
    (OriginalCutCalls.root_ne_ownBucket rows repeats i p (direction, terminal) a) _ _

theorem replaceValues_lowerCalls (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (values : Values rows repeats (.step i p) slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (fresh : H (cutSlots (.step i p) slots)) :
    (fun call => replaceValues rows repeats (.step i p) slots values a fresh (.inr call)) =
      replaceValues rows repeats p (childSlots slots i)
        (fun call => values (.inr call)) a fresh :=
  Function.update_comp_eq_of_injective' values Sum.inr_injective
    (OriginalCutCalls.ownBucket rows repeats p a) fresh

theorem selectedRows_reconstruct (rows repeats : Nat → Nat) :
    ∀ {n m : Nat} (p : Path branch n (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (exterior : Exterior rows repeats p slots) (values : Values rows repeats p slots)
      (below : BelowArrays rows p slots),
      SelectedArrayReplacement.selectedRows rows p slots
          (reconstruct rows repeats p slots exterior values below) =
        BucketSampler.evaluate (rows (m + 1)) (id : H (cutSlots p slots) → H (cutSlots p slots))
          (ownValues rows repeats p slots values) := by
  intro n
  induction n with
  | zero => intro m p; cases p
  | succ n ih =>
      intro m p slots exterior values below
      cases p with
      | refl => rfl
      | step i p =>
          change SelectedArrayReplacement.selectedRows rows (.step i p) slots
            (WholeArraySampler.assemble slots rows
              (reconstructBuckets rows repeats (.step i p) slots
                (fun direction terminal => values (.inl (direction, terminal))) exterior.1)
              (WholeArraySampler.childrenAt slots rows i
                (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                  (fun call => values (.inr call)) below) exterior.2.2)) = _
          rw [SelectedArrayReplacement.selectedRows_assemble_step]
          exact ih p (childSlots slots i) exterior.2.1 (fun call => values (.inr call)) below

theorem reconstruct_replaceValues (rows repeats : Nat → Nat) :
    ∀ {n m : Nat} (p : Path branch n (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (exterior : Exterior rows repeats p slots) (values : Values rows repeats p slots)
      (below : BelowArrays rows p slots)
      (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots)),
      reconstruct rows repeats p slots exterior
          (replaceValues rows repeats p slots values a fresh) below =
        SelectedArrayReplacement.replace rows p slots
          (reconstruct rows repeats p slots exterior values below)
          (BucketSampler.evaluate (rows (m + 1))
            (id : H (cutSlots p slots) → H (cutSlots p slots))
            (Function.update (ownValues rows repeats p slots values) a fresh)) := by
  intro n
  induction n with
  | zero => intro m p; cases p
  | succ n ih =>
      intro m p slots exterior values below a fresh
      cases p with
      | refl =>
          exact congrArg
            (fun buckets : BucketSampler.Direction (rows (n + 1)) → H slots =>
              WholeArraySampler.assemble slots rows
                (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots) buckets) below)
            (ownValues_replaceValues rows repeats (.refl (n + 1)) slots values a fresh)
      | step i p =>
          change WholeArraySampler.assemble slots rows
            (reconstructBuckets rows repeats (.step i p) slots
              (fun direction terminal =>
                replaceValues rows repeats (.step i p) slots values a fresh
                  (.inl (direction, terminal))) exterior.1)
            (WholeArraySampler.childrenAt slots rows i
              (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                (fun call => replaceValues rows repeats (.step i p) slots values a fresh
                  (.inr call)) below) exterior.2.2) =
            SelectedArrayReplacement.replace rows (.step i p) slots
              (WholeArraySampler.assemble slots rows
                (reconstructBuckets rows repeats (.step i p) slots
                  (fun direction terminal => values (.inl (direction, terminal))) exterior.1)
                (WholeArraySampler.childrenAt slots rows i
                  (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                    (fun call => values (.inr call)) below) exterior.2.2)) _
          rw [replaceValues_rootCalls, replaceValues_lowerCalls,
            SelectedArrayReplacement.replace_assemble_step]
          exact congrArg (fun selected => WholeArraySampler.assemble slots rows
            (reconstructBuckets rows repeats (.step i p) slots
              (fun direction terminal => values (.inl (direction, terminal))) exterior.1)
            (WholeArraySampler.childrenAt slots rows i selected exterior.2.2))
              (ih p (childSlots slots i) exterior.2.1
                (fun call => values (.inr call)) below a fresh)

def replaceRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots)) :
    Record rows repeats p slots :=
  (record.1, (replaceValues rows repeats p slots record.2.1 a fresh, record.2.2))

theorem reconstructRecord_replace_outside (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots))
    (node : Nodes branch n) (hnode : node ≠ WholeArrayInteriorExterior.upperNode p) :
    reconstructRecord rows repeats p slots (replaceRecord rows repeats p slots record a fresh) node =
      reconstructRecord rows repeats p slots record node := by
  change reconstruct rows repeats p slots record.1
    (replaceValues rows repeats p slots record.2.1 a fresh) record.2.2 node = _
  rw [reconstruct_replaceValues]
  exact SelectedArrayReplacement.replace_outside rows p slots _ _ node hnode

theorem reconstruct_outside_eq_of_nonown_eq (rows repeats : Nat → Nat) :
    ∀ {n m : Nat} (p : Path branch n (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (exterior : Exterior rows repeats p slots)
      (values₁ values₂ : Values rows repeats p slots) (below : BelowArrays rows p slots),
      (∀ call, (∀ a, call ≠ OriginalCutCalls.ownBucket rows repeats p a) →
        values₁ call = values₂ call) →
      ∀ node : Nodes branch n, node ≠ WholeArrayInteriorExterior.upperNode p →
        reconstruct rows repeats p slots exterior values₁ below node =
          reconstruct rows repeats p slots exterior values₂ below node := by
  intro n
  induction n with
  | zero => intro m p; cases p
  | succ n ih =>
      intro m p slots exterior values₁ values₂ below hvalues node hnode
      cases p with
      | refl =>
          cases node with
          | inl u => cases u; exact False.elim (hnode rfl)
          | inr pair => rfl
      | step i p =>
          have hroot : (fun direction terminal => values₁ (.inl (direction, terminal))) =
              (fun direction terminal => values₂ (.inl (direction, terminal))) := by
            funext direction terminal
            exact hvalues (.inl (direction, terminal))
              (fun a => OriginalCutCalls.root_ne_ownBucket rows repeats i p
                (direction, terminal) a)
          have hlower : ∀ call,
              (∀ a, call ≠ OriginalCutCalls.ownBucket rows repeats p a) →
              values₁ (.inr call) = values₂ (.inr call) := by
            intro call hcall
            apply hvalues (.inr call)
            intro a heq
            exact hcall a (Sum.inr.inj heq)
          cases node with
          | inl u =>
              cases u
              change reconstructBuckets rows repeats (.step i p) slots
                  (fun direction terminal => values₁ (.inl (direction, terminal))) exterior.1 =
                reconstructBuckets rows repeats (.step i p) slots
                  (fun direction terminal => values₂ (.inl (direction, terminal))) exterior.1
              rw [hroot]
          | inr pair =>
              rcases pair with ⟨child, node⟩
              by_cases hchild : child = i
              · subst child
                have hnode' : node ≠ WholeArrayInteriorExterior.upperNode p := by
                  intro h
                  exact hnode (congrArg (fun v => Sum.inr (i, v)) h)
                change WholeArraySampler.childrenAt slots rows i
                  (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                    (fun call => values₁ (.inr call)) below) exterior.2.2 i node =
                  WholeArraySampler.childrenAt slots rows i
                    (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                      (fun call => values₂ (.inr call)) below) exterior.2.2 i node
                rw [WholeArraySampler.childrenAt_selected,
                  WholeArraySampler.childrenAt_selected]
                exact ih p (childSlots slots i) exterior.2.1
                  (fun call => values₁ (.inr call)) (fun call => values₂ (.inr call))
                  below hlower node hnode'
              · change WholeArraySampler.childrenAt slots rows i
                  (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                    (fun call => values₁ (.inr call)) below) exterior.2.2 child node =
                  WholeArraySampler.childrenAt slots rows i
                    (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                      (fun call => values₂ (.inr call)) below) exterior.2.2 child node
                simp only [WholeArraySampler.childrenAt, dite_eq_right hchild]

theorem selectedRows_reconstructRecord_replace (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots)) :
    SelectedArrayReplacement.selectedRows rows p slots
        (reconstructRecord rows repeats p slots (replaceRecord rows repeats p slots record a fresh)) =
      SelectedArrayReplacement.selectedRows rows p slots
        (reconstructRecord rows repeats p slots record) +
          BucketSampler.rankOne a.val
            (fresh - record.2.1 (OriginalCutCalls.ownBucket rows repeats p a)) := by
  change SelectedArrayReplacement.selectedRows rows p slots
    (reconstruct rows repeats p slots record.1
      (replaceValues rows repeats p slots record.2.1 a fresh) record.2.2) =
    SelectedArrayReplacement.selectedRows rows p slots
      (reconstruct rows repeats p slots record.1 record.2.1 record.2.2) + _
  rw [selectedRows_reconstruct, selectedRows_reconstruct, ownValues_replaceValues,
    BucketSampler.evaluate_update]
  rfl

theorem selectedMatrix_reconstructRecord_replace (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots)) :
    EvaluationMatrix.ofRows (H (cutSlots p slots))
        (SelectedArrayReplacement.selectedRows rows p slots
          (reconstructRecord rows repeats p slots (replaceRecord rows repeats p slots record a fresh))) =
      EvaluationMatrix.shift (H (cutSlots p slots))
        (EvaluationMatrix.ofRows (H (cutSlots p slots))
          (SelectedArrayReplacement.selectedRows rows p slots
            (reconstructRecord rows repeats p slots record)))
        a.val (fresh - record.2.1 (OriginalCutCalls.ownBucket rows repeats p a)) := by
  change EvaluationMatrix.ofRows (H (cutSlots p slots))
    (SelectedArrayReplacement.selectedRows rows p slots
      (reconstruct rows repeats p slots record.1
        (replaceValues rows repeats p slots record.2.1 a fresh) record.2.2)) = _
  rw [selectedRows_reconstruct, ownValues_replaceValues]
  have hold := selectedRows_reconstruct rows repeats p slots record.1 record.2.1 record.2.2
  change SelectedArrayReplacement.selectedRows rows p slots
    (reconstructRecord rows repeats p slots record) = _ at hold
  rw [hold]
  exact BucketMatrixResampling.assembledMatrix_update (H (cutSlots p slots))
    (rows (m + 1)) (ownValues rows repeats p slots record.2.1) a fresh

end
end PerfectCompleteness.OriginalCutBucketReplacement

end

end OAI
