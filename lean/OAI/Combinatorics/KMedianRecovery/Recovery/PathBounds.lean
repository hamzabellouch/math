import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.MergePath

namespace OAI

namespace MetricKMedianRecovery.PhaseMergePath
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
lemma Good.length_bound {loc : D → X} {F B Q : Finset X} {copy : X → X}
    {v z lam eta : ℝ} {H : List X} (h : Good loc F B Q copy v z lam eta H) :
    H.length≤F.card+1 := by
  have hs : H.toFinset⊆F∪(H.toFinset\F) := by
    intro x hx
    by_cases hxF : x∈F
    · exact Finset.mem_union_left _ hxF
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx,hxF⟩)
  have hl := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  rw [List.toFinset_card_of_nodup h.1.1.nodup] at hl
  exact hl.trans (Nat.add_le_add_left h.2 F.card)
lemma Step.preserves {loc : D → X} {F B Q : Finset X} {copy : X → X}
    {v z lam : ℝ} {H G : List X} (h : Step loc F B Q copy v z lam H G)
    {P : X → Prop} (hF : ∀ x∈F,P x) (hc : ∀ x∈F,P (copy x)) (hH : ∀ x∈H,P x) :
    ∀ x∈G,P x := by
  cases h with
  | add H i hi=>
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hH x hx
    · obtain rfl:=List.mem_singleton.mp hx
      exact hc i hi
  | remove C T A i hi hA hreg=>
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · rcases List.mem_append.mp hx with hx|hx
      · exact hH x (List.mem_append_left _ hx)
      · exact hH x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    · exact hF x (hreg x hx)
  | replace C T i hi hn=>
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hH x (List.mem_append_left _ hx)
    · rcases List.mem_cons.mp hx with rfl|hx
      · exact hF x hi
      · exact hH x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
end MetricKMedianRecovery.PhaseMergePath

namespace MetricKMedianRecovery.CanonicalMergePath
open PhaseSequence PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
lemma Path.vertices_good {loc : D → X} {F B Q : Finset X} {copy : X → X}
    {v z lam eta : ℝ} {H J : List X} {T : List (List X)}
    (h : Path loc F B Q copy v z lam eta H T J) :
    ∀ G∈T,Good loc F B Q copy v z lam eta G := by
  induction h with
  | nil=>intro G hG; exact False.elim (List.not_mem_nil hG)
  | cons _ _ ht ih=>
    intro G hG
    rcases List.mem_cons.mp hG with rfl|hG
    · exact ht.toWalk.first_good
    · exact ih G hG
lemma Path.vertices_mem {loc : D → X} {F B Q : Finset X} {copy : X → X}
    {v z lam eta : ℝ} {H J : List X} {T : List (List X)}
    (h : Path loc F B Q copy v z lam eta H T J)
    {P : X → Prop} (hF : ∀ x∈F,P x) (hc : ∀ x∈F,P (copy x)) (hH : ∀ x∈H,P x) :
    ∀ G∈T,∀ x∈G,P x := by
  induction h with
  | nil=>intro G hG; exact False.elim (List.not_mem_nil hG)
  | cons _ e _ ih=>
    have hG:=e.preserves hF hc hH
    intro G hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact hG
    · exact ih hG G hm
end MetricKMedianRecovery.CanonicalMergePath

end OAI
