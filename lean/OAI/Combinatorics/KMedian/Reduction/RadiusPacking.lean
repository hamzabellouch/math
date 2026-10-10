import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem radius_packing {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (D : Finset X) (r : X → ℝ) (hpos : ∀ i ∈ D, 0 < r i) :
    ∃ P : Finset X, P ⊆ D ∧
      (∀ i ∈ P, ∀ j ∈ P, i ≠ j → r i ≤ dist i j) ∧
      (∀ i ∈ D, ∃ p ∈ P, dist i p < r p ∧ r i ≤ r p) := by
  classical
  revert hpos
  refine D.strongInductionOn ?_
  intro D ih hpos
  by_cases hD : D.Nonempty
  · obtain ⟨i,hi,hmax⟩ := D.exists_max_image r hD
    let E := D.filter (fun j => r i ≤ dist i j)
    have hED : E ⊆ D := filter_subset _ _
    have hiE : i ∉ E := by
      intro hh
      have ht := (mem_filter.mp hh).2
      rw [dist_self] at ht
      exact (hpos i hi).not_ge ht
    have hstrict : E ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hED,by
      intro hh
      exact hiE (hh ▸ hi)⟩
    obtain ⟨P,hPE,hsep,hcover⟩ := ih E hstrict (fun j hj => hpos j (hED hj))
    refine ⟨insert i P,insert_subset hi (hPE.trans hED),?_,?_⟩
    · intro a ha b hb hab
      obtain rfl | haP := mem_insert.mp ha
      · obtain rfl | hbP := mem_insert.mp hb
        · exact (hab rfl).elim
        · exact (mem_filter.mp (hPE hbP)).2
      · obtain rfl | hbP := mem_insert.mp hb
        · have hd := (mem_filter.mp (hPE haP)).2
          rw [dist_comm] at hd
          exact (hmax a (hED (hPE haP))).trans hd
        · exact hsep a haP b hbP hab
    · intro a ha
      by_cases haE : a ∈ E
      · obtain ⟨p,hp,hap,hr⟩ := hcover a haE
        exact ⟨p,mem_insert_of_mem hp,hap,hr⟩
      · have hdist : dist a i < r i := by
          have hn : ¬r i ≤ dist i a := by
            intro hh
            exact haE (mem_filter.mpr ⟨ha,hh⟩)
          simpa only [dist_comm] using lt_of_not_ge hn
        exact ⟨i,mem_insert_self _ _,hdist,hmax a ha⟩
  · refine ⟨∅,empty_subset _,?_,?_⟩
    · simp
    · intro i hi
      exact (hD ⟨i,hi⟩).elim

end MetricKMedian.Reduction
end
end

end OAI
