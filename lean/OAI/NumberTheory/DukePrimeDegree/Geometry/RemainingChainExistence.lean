import OAI.NumberTheory.DukePrimeDegree.Geometry.EliminationRootOrder

namespace OAI

/-! # Completing a remaining-root chart from any initial pattern -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_complete_chain_from_pattern {n : ℕ}
    (P : Finset (Fin n × Fin n)) (D : Finset (Fin n))
    (hP : InitialRootPattern P) (hD : PivotsFromPattern P D) :
    ∃ c : EliminationChain P D, c.finalEntries = allPositiveRoots n := by
  suffices H : ∀ m : ℕ, ∀ (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)),
      (allPositiveRoots n \ P).card = m → InitialRootPattern P → PivotsFromPattern P D →
      ∃ c : EliminationChain P D, c.finalEntries = allPositiveRoots n by
    exact H _ P D rfl hP hD
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro P D hcard hP hD
    by_cases he : allPositiveRoots n \ P = ∅
    · refine ⟨.done,?_⟩
      change P = allPositiveRoots n
      exact Finset.Subset.antisymm (fun p hp => (hP p hp).1)
        (Finset.sdiff_eq_empty_iff_subset.mp he)
    · obtain ⟨p,hp,hm⟩ := Finset.exists_min_image (allPositiveRoots n \ P)
        (fun q => toLex q) (Finset.nonempty_iff_ne_empty.mpr he)
      have hab : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
      have hn : p ∉ P := (Finset.mem_sdiff.mp hp).2
      have hless : (allPositiveRoots n \ insert p P).card < m := by
        rw [Finset.sdiff_insert,←hcard]
        exact Finset.card_erase_lt_of_mem hp
      obtain ⟨c,hc⟩ := ih _ hless (insert p P) (insert p.1 D) rfl
        (initialRootPattern_insert_min hP p hp hm) (pivotsFromPattern_insert hD p.1 p.2)
      exact ⟨.step p.1 p.2 (ne_of_lt hab) (initialRootPattern_stable hP hab hn)
        (initialRootPattern_pivot_notMem hP hD hab hn) c,hc⟩

namespace EliminationChain

lemma eq_done_of_completed {n : ℕ} {D : Finset (Fin n)}
    (c : EliminationChain (allPositiveRoots n) D)
    (hf : c.finalEntries = allPositiveRoots n) : c = .done := by
  have hpos : ∀ p ∈ c.finalEntries, p.1 < p.2 := by
    intro p hp
    rw [hf] at hp
    exact (Finset.mem_filter.mp hp).2
  have hnot := c.roots_notMem_initial hpos
  cases c with
  | done => rfl
  | step a b hab hP hb tail =>
    have hn := hnot (a,b) (by simp [roots])
    have hm : (a,b) ∈ allPositiveRoots n := by
      rw [←hf]
      exact tail.entries_subset_final (Finset.mem_insert_self _ _)
    exact (hn hm).elim

end EliminationChain
end DukePrimeDegree

end

end OAI
