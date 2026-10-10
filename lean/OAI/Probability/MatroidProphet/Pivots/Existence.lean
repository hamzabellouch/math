import OAI.Probability.MatroidProphet.Pivots.OccurrenceSupport

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α β : Type*} [Fintype β] [DecidableEq β]

lemma exists_pivot
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    (M : Matroid α) (label : β → α) (time : β → ℕ) {e : α}
    (hnonloop : e ∉ M.closure ∅) (hspan : e ∈ M.closure (Set.range label)) :
    ∃ o, IsPivot M label time e o := by
  classical
  let P := fun k => e ∈ M.closure (label '' {o | time o ≤ k})
  have hex : ∃ k, P k := by
    refine ⟨Finset.univ.sup time, M.closure_subset_closure ?_ hspan⟩
    rintro _ ⟨o, rfl⟩
    exact ⟨o, by
      change time o ≤ Finset.univ.sup time
      exact Finset.le_sup (Finset.mem_univ o), rfl⟩
  let k := Nat.find hex
  have hk : P k := Nat.find_spec hex
  have hnot : e ∉ M.closure (label '' {o | time o < k}) := by
    intro hn
    by_cases hk0 : k = 0
    · exact hnonloop (by simpa [hk0] using hn)
    have hprev : P (k - 1) := by
      apply M.closure_subset_closure ?_ hn
      rintro _ ⟨o, ho, rfl⟩
      exact ⟨o, by
        change time o ≤ k - 1
        change time o < k at ho
        omega, rfl⟩
    have hmin : k ≤ k - 1 := Nat.find_min' hex hprev
    omega
  have hat : ∃ o, time o = k := by
    by_contra h
    apply hnot
    apply M.closure_subset_closure ?_ hk
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨o, ?_, rfl⟩
    have hne : time o ≠ k := fun heq => h ⟨o, heq⟩
    change time o < k
    change time o ≤ k at ho
    omega
  obtain ⟨o, ho⟩ := hat
  exact ⟨o, by simpa [IsPivot, ho] using And.intro hk hnot⟩

lemma pivot_unique
    {α : Type u_1} {β : Type u_2} [Fintype β] [DecidableEq β]
    (M : Matroid α) (label : β → α) (time : β → ℕ)
    (htime : Function.Injective time) {e : α} {o p : β}
    (ho : IsPivot M label time e o) (hp : IsPivot M label time e p) : o = p := by
  apply htime
  apply le_antisymm
  · by_contra h
    apply ho.2
    apply M.closure_subset_closure ?_ hp.1
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, lt_of_le_of_lt ha (Nat.lt_of_not_ge h), rfl⟩
  · by_contra h
    apply hp.2
    apply M.closure_subset_closure ?_ ho.1
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, lt_of_le_of_lt ha (Nat.lt_of_not_ge h), rfl⟩

lemma existsUnique_pivot (M : Matroid α) (label : β → α) (time : β → ℕ)
    (htime : Function.Injective time) {e : α}
    (hnonloop : e ∉ M.closure ∅) (hspan : e ∈ M.closure (Set.range label)) :
    ∃! o, IsPivot M label time e o := by
  obtain ⟨o, ho⟩ := exists_pivot M label time hnonloop hspan
  exact ⟨o, ho, fun p hp => pivot_unique M label time htime hp ho⟩

end Pivots
end MatroidProphet

end OAI
