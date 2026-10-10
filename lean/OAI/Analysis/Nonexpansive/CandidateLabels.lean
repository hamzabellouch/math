import OAI.Analysis.Nonexpansive.CandidateStages
import OAI.Analysis.Nonexpansive.GlobalCandidateOrdinals

namespace OAI

/-!
# Actual global labels of the retained candidates

Within a parent, the original positive-support embedding keeps the candidate
indices.  Concatenation preserves the parent order.  The stage's base counter
then places this entire finite sequence after all preceding sequences.  Consequently
the labels are globally injective even though zero-weight candidates leave
gaps among the labels of retained children.
-/

noncomputable section

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace CandidateContext

variable {D : NormalizedMinimalData (X := X)} (C : CandidateContext D)
variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (hanchor : C.anchor = A.x)

/-- Retained children keep their positions in the complete candidate sequence. -/
def retainedCandidate :
    Fin (C.selectedExtension A hanchor).size ↪o Fin (C.candidateCount A hanchor) :=
  OrderedGroupConcat.retain
    (fun p => (C.group A hanchor C.runTolerance_pos p).retain)

@[simp] theorem retainedCandidate_group (p : Fin C.frontier.size)
    (j : Fin (C.group A hanchor C.runTolerance_pos p).q) :
    C.retainedCandidate A hanchor
      (OrderedGroupConcat.group
        (fun p => (C.group A hanchor C.runTolerance_pos p).q) p j) =
      OrderedGroupConcat.group
        (fun p => (C.group A hanchor C.runTolerance_pos p).N) p
        ((C.group A hanchor C.runTolerance_pos p).retain j) :=
  OrderedGroupConcat.retain_group
    (fun p => (C.group A hanchor C.runTolerance_pos p).retain) p j

/-- The original candidate index has exactly the same parent as its child. -/
theorem retainedCandidate_parent (v : Fin (C.selectedExtension A hanchor).size) :
    OrderedGroupConcat.parent
      (fun p => (C.group A hanchor C.runTolerance_pos p).N)
      (C.retainedCandidate A hanchor v) =
      (C.selectedExtension A hanchor).parent v :=
  OrderedGroupConcat.parent_retain
    (fun p => (C.group A hanchor C.runTolerance_pos p).retain) v

/-- The retained node uses the same actual map as the corresponding full candidate. -/
theorem retainedCandidate_map (v : Fin (C.selectedExtension A hanchor).size) :
    FrontierExtension.groupValue
      (fun p => (C.group A hanchor C.runTolerance_pos p).N)
      (fun p i => (C.group A hanchor C.runTolerance_pos p).selected i)
      (C.retainedCandidate A hanchor v) =
      (C.selectedExtension A hanchor).map v := by
  obtain ⟨⟨p, j⟩, rfl⟩ :=
    (OrderedGroupConcat.equiv
      (fun p => (C.group A hanchor C.runTolerance_pos p).q)).surjective v
  change FrontierExtension.groupValue _ _
    (C.retainedCandidate A hanchor (OrderedGroupConcat.group _ p j)) =
    (C.selectedExtension A hanchor).map (OrderedGroupConcat.group _ p j)
  rw [retainedCandidate_group, FrontierExtension.groupValue_group]
  exact (C.levelExtension_map_group A hanchor C.runTolerance_pos p j).symm

end CandidateContext

namespace AnchoredCandidateContext

variable (D : NormalizedMinimalData (X := X))
variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (U : Ultrafilter ℕ)

/-- Transport the retained embedding to the actual next level of the infinite tree. -/
def retainedCandidate (k : ℕ) :
    (tower D A U).toOrderedTree.Node (k + 1) ↪o
      Fin ((context D A U k).candidateCount A (context_anchor D A U k)) :=
  OrderEmbedding.ofStrictMono
    (fun v => (context D A U k).retainedCandidate A (context_anchor D A U k)
      ((tower D A U).nextNode k v)) (by
        intro a b hab
        apply ((context D A U k).retainedCandidate A
          (context_anchor D A U k)).strictMono
        exact hab)

@[simp] theorem retainedCandidate_apply (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    retainedCandidate D A U k v =
      (context D A U k).retainedCandidate A (context_anchor D A U k)
        ((tower D A U).nextNode k v) := rfl

/-- The original global candidate ordinal, with no renumbering after retention. -/
def candidateLabel (v : (tower D A U).toOrderedTree.NonrootNode) : ℕ :=
  (context D A U v.1).base + (retainedCandidate D A U v.1 v.2).val

@[simp] theorem candidateLabel_apply (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    candidateLabel D A U ⟨k, v⟩ =
      (context D A U k).base + (retainedCandidate D A U k v).val := rfl

/-- Exact ordinal of a retained member of a particular parent group. -/
theorem candidateLabel_group (k : ℕ) (p : Fin (context D A U k).frontier.size)
    (j : Fin ((context D A U k).group A (context_anchor D A U k)
      (context D A U k).runTolerance_pos p).q) :
    candidateLabel D A U
      ⟨k, ((tower D A U).nextNode k).symm
        (OrderedGroupConcat.group
          (fun p => ((context D A U k).group A (context_anchor D A U k)
            (context D A U k).runTolerance_pos p).q) p j)⟩ =
      (context D A U k).base +
        OrderedGroupConcat.offset
          (fun p => ((context D A U k).group A (context_anchor D A U k)
            (context D A U k).runTolerance_pos p).N) p +
        (((context D A U k).group A (context_anchor D A U k)
          (context D A U k).runTolerance_pos p).retain j).val := by
  let v : Fin ((tower D A U).step k).size :=
    OrderedGroupConcat.group
      (fun p => ((context D A U k).group A (context_anchor D A U k)
        (context D A U k).runTolerance_pos p).q) p j
  exact
    (congrArg
      (fun w : Fin ((tower D A U).step k).size =>
        (context D A U k).base +
          ((context D A U k).retainedCandidate A (context_anchor D A U k) w).val)
      (Equiv.apply_symm_apply ((tower D A U).nextNode k) v)).trans
      ((congrArg (fun i : ℕ => (context D A U k).base + i)
        (OrderedGroupConcat.retain_group_val
          (fun p => ((context D A U k).group A (context_anchor D A U k)
            (context D A U k).runTolerance_pos p).retain) p j)).trans
        (Nat.add_assoc _ _ _).symm)

/-- The concrete candidate counter never decreases between stages. -/
theorem context_base_monotone : Monotone (fun k => (context D A U k).base) :=
  GlobalCandidateOrdinals.base_monotone
    (fun k => (context D A U k).base)
    (fun k => (context D A U k).candidateCount A (context_anchor D A U k))
    (context_base_succ D A U)

/-- Every retained label lies in its actual stage's complete candidate interval. -/
theorem candidateLabel_lt_next_base (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    candidateLabel D A U ⟨k, v⟩ < (context D A U (k + 1)).base := by
  rw [candidateLabel_apply, context_base_succ]
  exact Nat.add_lt_add_left (retainedCandidate D A U k v).isLt _

theorem context_base_le_candidateLabel (k : ℕ)
    (v : (tower D A U).toOrderedTree.Node (k + 1)) :
    (context D A U k).base ≤ candidateLabel D A U ⟨k, v⟩ := by
  rw [candidateLabel_apply]
  exact Nat.le_add_right _ _

/-- Every candidate from an earlier level precedes the current base counter. -/
theorem candidateLabel_lt_base_of_lt {i k : ℕ} (hik : i < k)
    (v : (tower D A U).toOrderedTree.Node (i + 1)) :
    candidateLabel D A U ⟨i, v⟩ < (context D A U k).base :=
  (candidateLabel_lt_next_base D A U i v).trans_le
    (context_base_monotone D A U (Nat.succ_le_of_lt hik))

/-- Global injectivity follows from the actual counter recurrence and the
proved within-level retained embeddings. -/
theorem candidateLabel_injective : Function.Injective (candidateLabel D A U) :=
  GlobalCandidateOrdinals.label_injective
    (fun k => (context D A U k).base)
    (context_base_succ D A U) (retainedCandidate D A U)

end AnchoredCandidateContext
end ReflexiveFixedPoints

end

end OAI
