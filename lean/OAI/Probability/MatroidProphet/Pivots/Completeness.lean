import OAI.Probability.MatroidProphet.Pivots.Guarantee
import OAI.Probability.MatroidProphet.Pivots.Existence

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α] {r q n : ℕ}

lemma recordsPivots_exists
    {α : Type u_1} [Fintype α] {r : ℕ} {q : ℕ} {n : ℕ} (M : Matroid α) (label : Occurrence r q → α)
    (test : Fin n → α) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool)
    (hnonloop : ∀ f, test f ∉ M.closure ∅)
    (hspan : ∀ f, test f ∈ M.closure (Set.range label)) :
    ∃ t, RecordsPivots M label test time oldMark movableMark t := by
  classical
  choose pivot hpivot using fun f => exists_pivot M label time (hnonloop f) (hspan f)
  refine ⟨Finset.univ.filter (fun f => occurrenceMark oldMark movableMark (pivot f) = true), ?_⟩
  intro f
  exact ⟨pivot f, hpivot f, by simp⟩

lemma recorded_pattern_exists_of_old_spanning (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (oldMark : Fin r → Bool)
    (holdspan : M.closure (oldPrefix b r) = M.E)
    (htest : ∀ f, test f ∈ M.E ∧ test f ∉ M.closure ∅)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time) (htime : Function.Injective time)
    (movableMark : Fin q → Bool) :
    ∃ t ∈ markedPivotPatterns M b a test oldMark,
      RecordsPivots M (occurrenceLabel b a) test time oldMark movableMark t := by
  classical
  have hspan : ∀ f, test f ∈ M.closure (Set.range (occurrenceLabel (r := r) b a)) := by
    intro f
    have htest' : test f ∈ M.closure (oldPrefix b r) := holdspan.symm ▸ (htest f).1
    apply M.closure_subset_closure ?_ htest'
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨Sum.inl ⟨k, hk⟩, rfl⟩
  obtain ⟨t, ht⟩ := recordsPivots_exists M (occurrenceLabel b a) test time oldMark movableMark
    (fun f => (htest f).2) hspan
  exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, time, horder, htime, movableMark, ht⟩, ht⟩

end Pivots
end MatroidProphet

end OAI
