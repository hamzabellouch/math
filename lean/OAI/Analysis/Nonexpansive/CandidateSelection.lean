import OAI.Analysis.Nonexpansive.CandidateRecords
import OAI.Analysis.Nonexpansive.CandidatePreparation
import OAI.Analysis.Nonexpansive.SequentialHistory
import OAI.Analysis.Nonexpansive.AdaptiveParentReturn
import OAI.Analysis.Nonexpansive.AnchorAdaptiveSelection

namespace OAI

/-!
# Actual adaptive selection of one parent's candidate group

Every state carries a valid complete candidate history. Its threshold is
computed from that history before the next map is chosen. The actual compact
detector then produces a legal new record. The adaptive anchor chooses a
finite return, and only afterward does positive-support extraction select
its children. Neither candidate existence nor a return law is assumed.
-/

noncomputable section

open Set
open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace CandidateContext

variable {D : NormalizedMinimalData (X := X)} (C : CandidateContext D)

/-- The type used by adaptive selection contains only valid immutable histories. -/
abbrev State := HistoryState (CandidateRecord C) C.Legal

/-- A threshold prepared solely from the existing history works for every
map in its actual resolvent tail. Auxiliary records are selected afterward. -/
theorem exists_threshold (p : Fin C.frontier.size)
    (history : List (CandidateRecord C)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ g : D.K → D.K,
      g ∈ tailFamily D.closed D.convex D.T D.nonexpansive m →
      ∃ r : CandidateRecord C, r.parent = p ∧ r.map = g ∧ C.Legal history r := by
  obtain ⟨m, hm, hprepared⟩ := exists_prepared_candidate_threshold D C.frontier
    (C.historyParent history) (C.historyPoint history) C.terminal C.ultrafilter C.depth
    (C.candidateAncestorMap p) (C.candidateAncestorMap_generated p) (C.nextBudget_pos history)
  refine ⟨m, hm, ?_⟩
  intro g hg
  obtain ⟨hgenerated, houtput⟩ := hprepared g hg
  obtain ⟨f, hf, hsep, hanc⟩ := houtput C.anchor
  exact ⟨⟨p, g, hgenerated, f⟩, rfl, rfl, hf, hsep, hanc⟩

/-- No selected map or convex coefficient is an argument to this threshold. -/
def threshold (p : Fin C.frontier.size) (_i : ℕ) (s : C.State) : ℕ :=
  Classical.choose (C.exists_threshold p s.entries)

theorem threshold_pos (p : Fin C.frontier.size) (i : ℕ) (s : C.State) :
    1 ≤ C.threshold p i s :=
  (Classical.choose_spec (C.exists_threshold p s.entries)).1

/-- One transition appends exactly one actual selected map and its detector. -/
def Transition (p : Fin C.frontier.size) (_i : ℕ)
    (s : C.State) (g : D.K → D.K) (s' : C.State) : Prop :=
  ∃ r : CandidateRecord C, r.parent = p ∧ r.map = g ∧
    ∃ h : C.Legal s.entries r, s' = s.append r h

/-- Post-map auxiliary selection is total on the valid state type. -/
theorem exists_transition (p : Fin C.frontier.size) (i : ℕ) (s : C.State)
    (g : D.K → D.K)
    (hg : g ∈ tailFamily D.closed D.convex D.T D.nonexpansive (C.threshold p i s)) :
    ∃ s', C.Transition p i s g s' := by
  obtain ⟨r, hp, hmap, hlegal⟩ :=
    (Classical.choose_spec (C.exists_threshold p s.entries)).2 g hg
  exact ⟨s.append r hlegal, r, hp, hmap, hlegal, rfl⟩

theorem transition_length {p : Fin C.frontier.size} {i : ℕ} {s s' : C.State}
    {g : D.K → D.K} (h : C.Transition p i s g s') :
    s'.entries.length = s.entries.length + 1 := by
  obtain ⟨r, _, _, hr, rfl⟩ := h
  exact s.append_length r hr

/-- Earlier entries survive a legal transition literally. -/
theorem transition_take {p : Fin C.frontier.size} {i : ℕ} {s s' : C.State}
    {g : D.K → D.K} (h : C.Transition p i s g s') :
    s'.entries.take s.entries.length = s.entries := by
  obtain ⟨r, _, _, hr, rfl⟩ := h
  simp only [HistoryState.append_entries, List.take_append_of_le_length le_rfl,
    List.take_length]

/-- Every parent return retains the full states and candidates, including
candidates subsequently assigned coefficient zero. -/
abbrev ParentReturn (p : Fin C.frontier.size) (initial : C.State) (τ : ℝ) :=
  AdaptiveParentReturn (fun g : D.K → D.K => g C.anchor)
    (tailFamily D.closed D.convex D.T D.nonexpansive) C.anchor
    (C.threshold p) (C.Transition p) initial τ

/-- The actual anchor discharges all analytic inputs to adaptive selection. -/
def selectParent
    (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
    (hanchor : C.anchor = A.x) (p : Fin C.frontier.size)
    (initial : C.State) {τ : ℝ} (hτ : 0 < τ) : C.ParentReturn p initial τ := by
  letI : TopologicalSpace.MetrizableSpace (WeakCarrier D.K) := D.weak_metrizable
  apply adaptive_parent_return (fun g : D.K → D.K => g C.anchor)
    (tailFamily D.closed D.convex D.T D.nonexpansive) C.anchor A.D
    A.D_subset ?_ ?_ (C.threshold p) (C.threshold_pos p)
    (C.Transition p) initial (C.exists_transition p) hτ
  · simpa only [hanchor] using A.mem_closedConvexHull
  · intro m hm d
    simpa only [hanchor] using A.tail_closure m hm d

end CandidateContext
end ReflexiveFixedPoints

end

end OAI
