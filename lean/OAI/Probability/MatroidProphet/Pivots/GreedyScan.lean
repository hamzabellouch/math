import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Data.Finset.Max

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

noncomputable def keptOccurrences (M : Matroid α) (label : β → α) (time : β → ℕ) :
    Finset β := by
  classical
  exact Finset.univ.filter (fun o => label o ∉ M.closure (label '' {p | time p < time o}))

lemma mem_closure_kept_upto (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (o : β) :
    label o ∈ M.closure (label '' {p | p ∈ keptOccurrences M label time ∧ time p ≤ time o}) := by
  classical
  have aux : ∀ k, ∀ o, time o = k →
      label o ∈ M.closure (label '' {p | p ∈ keptOccurrences M label time ∧ time p ≤ k}) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro o ho
      by_cases hkeep : o ∈ keptOccurrences M label time
      · exact M.mem_closure_of_mem ⟨o, ⟨hkeep, ho.le⟩, rfl⟩
          (by rintro _ ⟨p, _, rfl⟩; exact hground p)
      have hdep : label o ∈ M.closure (label '' {p | time p < time o}) := by
        simpa [keptOccurrences] using hkeep
      apply M.closure_subset_closure_of_subset_closure ?_ hdep
      rintro _ ⟨p, hp, rfl⟩
      have hpk : time p < k := by simpa [ho] using hp
      have hih := ih (time p) hpk p rfl
      apply M.closure_subset_closure ?_ hih
      rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
      exact ⟨q, ⟨hq, hqt.trans hpk.le⟩, rfl⟩
  exact aux (time o) o rfl

lemma greedy_prefix_closure (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (k : ℕ) :
    M.closure (label '' {o | time o < k}) =
      M.closure (label '' {o | o ∈ keptOccurrences M label time ∧ time o < k}) := by
  classical
  apply Set.Subset.antisymm
  · apply M.closure_subset_closure_of_subset_closure
    rintro _ ⟨o, ho, rfl⟩
    apply M.closure_subset_closure ?_ (mem_closure_kept_upto M label time hground o)
    rintro _ ⟨p, ⟨hp, hpt⟩, rfl⟩
    exact ⟨p, ⟨hp, lt_of_le_of_lt hpt ho⟩, rfl⟩
  · apply M.closure_subset_closure
    rintro _ ⟨o, ⟨_, ho⟩, rfl⟩
    exact ⟨o, ho, rfl⟩

private lemma indep_image_of_notMem_prior
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β] (M : Matroid α) (label : β → α)
    (time : β → ℕ) (htime : Function.Injective time) (s : Finset β)
    (hground : ∀ o ∈ s, label o ∈ M.E)
    (hprior : ∀ o ∈ s, label o ∉ M.closure (label '' {p | p ∈ s ∧ time p < time o})) :
    M.Indep (label '' (s : Set β)) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · simp [hs]
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image s time (Finset.nonempty_iff_ne_empty.mpr hs)
    have hI := ih (s.erase p) (Finset.erase_ssubset hp)
      (fun o ho => hground o (Finset.mem_of_mem_erase ho)) (by
        intro o ho hmem
        apply hprior o (Finset.mem_of_mem_erase ho)
        apply M.closure_subset_closure ?_ hmem
        rintro _ ⟨q, ⟨hq, hqt⟩, rfl⟩
        exact ⟨q, ⟨Finset.mem_of_mem_erase hq, hqt⟩, rfl⟩)
    have hnot : label p ∉ M.closure (label '' (s.erase p : Set β)) := by
      intro hmem
      apply hprior p hp
      apply M.closure_subset_closure ?_ hmem
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨q, ⟨Finset.mem_of_mem_erase hq, ?_⟩, rfl⟩
      apply lt_of_le_of_ne (hmax q (Finset.mem_of_mem_erase hq))
      intro htimeeq
      exact (Finset.ne_of_mem_erase hq) (htime htimeeq)
    have hins := hI.insert_indep_iff.mpr (Or.inl ⟨hground p hp, hnot⟩)
    have hset : insert (label p) (label '' (s.erase p : Set β)) = label '' (s : Set β) := by
      rw [← Set.image_insert_eq, ← Finset.coe_insert, Finset.insert_erase hp]
    rwa [hset] at hins

lemma keptOccurrences_indep (M : Matroid α) (label : β → α) (time : β → ℕ)
    (hground : ∀ o, label o ∈ M.E) (htime : Function.Injective time) :
    M.Indep (label '' (keptOccurrences M label time : Set β)) := by
  classical
  apply indep_image_of_notMem_prior M label time htime
  · intro o _
    exact hground o
  · intro o ho hmem
    have hn := (Finset.mem_filter.mp ho).2
    apply hn
    apply M.closure_subset_closure ?_ hmem
    rintro _ ⟨p, ⟨_, hpt⟩, rfl⟩
    exact ⟨p, hpt, rfl⟩

end Pivots
end MatroidProphet

end OAI
