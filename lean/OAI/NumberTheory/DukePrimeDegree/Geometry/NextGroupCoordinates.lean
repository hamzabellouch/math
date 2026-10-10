import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingEuclideanCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootRowProduct

namespace OAI

/-! # Entry-coordinate homeomorphism for the next remaining root group -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

lemma next_initial (q : InitialRootStep n) : InitialRootPattern (insert q.root q.processed) :=
  initialRootPattern_insert_min q.initial q.root q.mem_remaining q.least

lemma next_closed (q : InitialRootStep n) : ∀ a b c : Fin n,
    (a,b) ∈ q.remaining.erase q.root → (b,c) ∈ q.remaining.erase q.root →
    (a,c) ∈ q.remaining.erase q.root := by
  simpa only [remaining,initialRemaining_erase] using
    initialRemaining_roots_closed (insert q.root q.processed) q.next_initial

lemma exists_nextGroupCoordinates (q : InitialRootStep n) :
    ∃ E : positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ (q.NextRoot → ℝ),
      ∀ g p, E g p = g.val.val p.val.1 p.val.2 := by
  obtain ⟨c,hc⟩ := exists_complete_elimination_chain_from_initial
    (insert q.root q.processed) ∅ q.next_initial (by intro a ha; simp at ha)
  have h : ∃ E : positiveRootGeneratedGroup (allPositiveRoots n \ insert q.root q.processed) ≃ₜ
      (↥(allPositiveRoots n \ insert q.root q.processed) → ℝ),
      ∀ g p, E g p = g.val.val p.val.1 p.val.2 :=
    ⟨c.remainingGroupCoordinates q.next_initial hc,c.remainingGroupCoordinates_apply q.next_initial hc⟩
  have hT : allPositiveRoots n \ insert q.root q.processed = q.remaining.erase q.root :=
    (initialRemaining_erase q.processed q.root).symm
  rw [hT] at h
  exact h

def nextGroupCoordinates (q : InitialRootStep n) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ (q.NextRoot → ℝ) :=
  q.exists_nextGroupCoordinates.choose

lemma nextGroupCoordinates_apply (q : InitialRootStep n)
    (g : positiveRootGeneratedGroup (q.remaining.erase q.root)) (p : q.NextRoot) :
    q.nextGroupCoordinates g p = g.val.val p.val.1 p.val.2 :=
  q.exists_nextGroupCoordinates.choose_spec g p

end InitialRootStep
end DukePrimeDegree

end

end OAI
