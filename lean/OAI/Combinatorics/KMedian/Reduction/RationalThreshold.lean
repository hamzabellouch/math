import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem representative_threshold (Q : Finset ℚ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ∈ insert 0 Q, 0 ≤ r ∧ (r:ℝ) ≤ B ∧
      ∀ q ∈ Q, ((q:ℝ) ≤ B ↔ q ≤ r) := by
  classical
  let A : Finset ℚ := insert 0 (Q.filter (fun q : ℚ => (q:ℝ) ≤ B))
  have hA : A.Nonempty := insert_nonempty _ _
  let r := A.max' hA
  have hr : r ∈ A := max'_mem A hA
  have hrB : (r:ℝ) ≤ B := by
    rcases mem_insert.mp hr with hr | hr
    · rw [hr,Rat.cast_zero]; exact hB
    · exact (mem_filter.mp hr).2
  refine ⟨r,?_,?_,hrB,?_⟩
  · rcases mem_insert.mp hr with hr | hr
    · exact mem_insert.mpr (Or.inl hr)
    · exact mem_insert_of_mem (mem_filter.mp hr).1
  · exact le_max' A 0 (mem_insert_self _ _)
  · intro q hq
    constructor
    · intro hqB
      exact le_max' A q (mem_insert_of_mem (mem_filter.mpr ⟨hq,hqB⟩))
    · intro hqr
      exact (show (q:ℝ) ≤ (r:ℝ) by exact_mod_cast hqr).trans hrB

def deletionChoices {I : Type} [DecidableEq I] (T : Finset I) (c : ℕ) : Finset (Finset I) :=
  (range (c+1)).biUnion (fun m => T.powersetCard m)

theorem mem_deletionChoices {I : Type} [DecidableEq I] (T D : Finset I) (c : ℕ) :
    D ∈ deletionChoices T c ↔ D ⊆ T ∧ D.card ≤ c := by
  simp only [deletionChoices,mem_biUnion,mem_range,mem_powersetCard]
  constructor
  · rintro ⟨m,hm,hsub,hcard⟩
    exact ⟨hsub,by omega⟩
  · rintro ⟨hsub,hcard⟩
    exact ⟨D.card,by omega,hsub,rfl⟩

theorem card_deletionChoices {I : Type} [DecidableEq I] (T : Finset I) (c : ℕ) :
    (deletionChoices T c).card ≤ (c+1)*(T.card+1)^c := by
  apply (card_biUnion_le).trans
  calc
    (∑ m ∈ range (c+1), (T.powersetCard m).card) ≤
        ∑ _m ∈ range (c+1), (T.card+1)^c := by
      apply sum_le_sum
      intro m hm
      rw [card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (Nat.le_succ _) m).trans
        (Nat.pow_le_pow_right (by omega) (by simpa only [mem_range,Nat.lt_succ_iff] using hm)))
    _ = (c+1)*(T.card+1)^c := by simp

end MetricKMedian.Reduction
end
end

end OAI
