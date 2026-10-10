import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Entry

namespace OAI

namespace MetricKMedianRecovery
namespace PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
namespace Entry
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {i : X}
lemma mono (h : Entry loc F B Q v z lam eta i) (hQ : Q' ⊆ Q) :
    Entry loc F B Q' v z lam eta i := by
  refine ⟨fun hi => h.1 (hQ hi),?_⟩
  rcases h.2 with hb|⟨hi,W,hW,hWF,hop⟩
  · exact Or.inl hb
  · exact Or.inr ⟨hi,W,hQ.trans hW,hWF,hop⟩
lemma mem (h : Entry loc F B Q v z lam eta i) : i ∈ F ∪ B := by
  rcases h.2 with h|h
  · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ h.1
end Entry

namespace Prefix
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {H G : List X}
lemma mono (h : Prefix loc F B v z lam eta Q H) (hQ : Q' ⊆ Q) :
    Prefix loc F B v z lam eta Q' H := by
  induction h generalizing Q' with
  | nil => exact Prefix.nil _
  | cons hi ht ih => exact Prefix.cons (hi.mono hQ) (ih (Finset.insert_subset_insert _ hQ))

lemma sublist (h : Prefix loc F B v z lam eta Q H) (hGH : G.Sublist H) :
    Prefix loc F B v z lam eta Q G := by
  induction hGH generalizing Q with
  | slnil => exact Prefix.nil _
  | cons a hGH ih =>
    cases h with
    | cons hi ht => exact (ih ht).mono (Finset.subset_insert _ _)
  | cons_cons a hGH ih =>
    cases h with
    | cons hi ht => exact Prefix.cons hi (ih ht)

lemma append (h : Prefix loc F B v z lam eta Q H)
    (hG : Prefix loc F B v z lam eta (Q ∪ H.toFinset) G) :
    Prefix loc F B v z lam eta Q (H++G) := by
  induction h with
  | nil => simpa using hG
  | @cons Q i H hi ht ih =>
    apply Prefix.cons hi
    apply ih
    simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hG

lemma opened_subset (h : Prefix loc F B v z lam eta Q H) : H.toFinset ⊆ F ∪ B := by
  intro i hi
  induction h with
  | nil => simp at hi
  | cons ha ht ih =>
    simp only [List.toFinset_cons,Finset.mem_insert] at hi
    rcases hi with rfl|hi
    · exact ha.mem
    · exact ih hi

lemma disjoint (h : Prefix loc F B v z lam eta Q H) : Disjoint Q H.toFinset := by
  induction h with
  | nil => simp
  | @cons Q i H hi ht ih =>
    rw [List.toFinset_cons,Finset.disjoint_insert_right]
    exact ⟨hi.1,Finset.disjoint_of_subset_left (Finset.subset_insert _ _) ih⟩

lemma nodup (h : Prefix loc F B v z lam eta Q H) : H.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons Q i H hi ht ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hm
    exact Finset.disjoint_left.mp ht.disjoint (Finset.mem_insert_self _ _)
      (List.mem_toFinset.mpr hm)
end Prefix

omit [DecidableEq X] in
lemma exact_opening_eta {loc : D → X} {F W : Finset X} {v z lam eta : ℝ} {i : X}
    (h : etaOpenable loc F W (1-3*v) (1+v^2) v z lam 0 i) (heta : 0 ≤ eta) :
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i := by
  obtain ⟨tau,hb,hp,hd⟩ := h
  refine ⟨tau,hb,?_,hd⟩
  have hn : 0 ≤ (Fintype.card D:ℝ)*eta := mul_nonneg (Nat.cast_nonneg _) heta
  simp only [mul_zero,sub_zero] at hp
  exact (sub_le_self lam hn).trans hp

theorem complete (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) :
    ∃ H : List X, Prefix loc F B v z lam eta Q H ∧
      (∀ i ∈ H, i ∈ F) ∧ Maximal loc F (Q ∪ H.toFinset) v z lam := by
  classical
  generalize heq : (F \ Q).card = fuel
  induction fuel using Nat.strong_induction_on generalizing Q with
  | h fuel ih =>
    by_cases hmax : Maximal loc F Q v z lam
    · exact ⟨[],Prefix.nil Q,by simp,by simpa using hmax⟩
    · simp only [Maximal,not_forall,not_not] at hmax
      obtain ⟨i,hi,hin,hop⟩ := hmax
      have hmem : i ∈ F \ Q := Finset.mem_sdiff.mpr ⟨hi,hin⟩
      have he : F \ insert i Q = (F \ Q).erase i := by
        ext f
        simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase]
        tauto
      have hdrop : (F \ insert i Q).card < fuel := by
        rw [he,← heq]
        exact Finset.card_erase_lt_of_mem hmem
      have hQ' : insert i Q ⊆ F ∪ B :=
        Finset.insert_subset (Finset.mem_union_left B hi) hQ
      obtain ⟨H,hH,hreg,hmax⟩ := ih (F \ insert i Q).card hdrop (insert i Q) hQ' rfl
      refine ⟨i::H,Prefix.cons ⟨hin,Or.inr ⟨hi,Q,Finset.Subset.refl _,hQ,
        exact_opening_eta hop heta⟩⟩ hH,?_,?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl|hx
        · exact hi
        · exact hreg _ hx
      · simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hmax

theorem complete_after (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B) (H : List X)
    (hH : Prefix loc F B v z lam eta Q H) :
    ∃ G : List X, G.length ≤ (F \ (Q ∪ H.toFinset)).card ∧
      (∀ i ∈ G, i ∈ F) ∧ Valid loc F B Q v z lam eta (H++G) := by
  obtain ⟨G,hG,hreg,hmax⟩ := complete loc F B (Q ∪ H.toFinset) v z lam eta heta
    (Finset.union_subset hQ hH.opened_subset)
  have hsub : G.toFinset ⊆ F \ (Q ∪ H.toFinset) := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨hreg _ (List.mem_toFinset.mp hi),?_⟩
    intro hmem
    exact Finset.disjoint_left.mp hG.disjoint hmem hi
  have hlen : G.length ≤ (F \ (Q ∪ H.toFinset)).card := by
    rw [← List.toFinset_card_of_nodup hG.nodup]
    exact Finset.card_le_card hsub
  refine ⟨G,hlen,hreg,hH.append hG,?_⟩
  simpa only [List.toFinset_append,← Finset.union_assoc] using hmax

end PhaseSequence
end MetricKMedianRecovery

end OAI
