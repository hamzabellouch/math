import OAI.Probability.MatroidProphet.CandidateFilter
import OAI.Probability.MatroidProphet.WeightedAccounting

namespace OAI

namespace MatroidProphet

open Finset

variable {n : ℕ}

noncomputable def weightLevels (a : Fin n → Option ℤ) (U : Finset (Fin n)) : Finset ℤ :=
  U.biUnion fun e => (a e).toFinset

lemma mem_weightLevels (a : Fin n → Option ℤ) (U : Finset (Fin n)) (i : ℤ) :
    i ∈ weightLevels a U ↔ ∃ e ∈ U, a e = some i := by
  classical
  simp [weightLevels]

lemma sum_weightGroups (a : Fin n → Option ℤ) (U : Finset (Fin n))
    (levels : Finset ℤ) (hlevels : weightLevels a U ⊆ levels)
    (f : ℤ → ℝ) :
    (∑ i ∈ levels, f i * ((U.filter fun e => a e = some i).card : ℝ)) =
      ∑ e ∈ U, (a e).elim 0 f := by
  classical
  have heq (i : ℤ) : f i * ((U.filter fun e => a e = some i).card : ℝ) =
      ∑ e ∈ U, if a e = some i then f i else 0 := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp_rw [heq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  cases ha : a e with
  | none => simp
  | some i =>
    have hi : i ∈ levels := hlevels ((mem_weightLevels a U i).2 ⟨e, he, ha⟩)
    simp [hi]

lemma sum_weightGroups_mass (a : Fin n → Option ℤ) (U : Finset (Fin n))
    (levels : Finset ℤ) (hlevels : weightLevels a U ⊆ levels) (B : ℝ) :
    (∑ i ∈ levels, B ^ i * ((U.filter fun e => a e = some i).card : ℝ)) =
      ∑ e ∈ U, levelWeight B (a e) := by
  rw [sum_weightGroups a U levels hlevels]
  apply Finset.sum_congr rfl
  intro e _
  cases a e <;> rfl

lemma highGroup_card (a : Fin n → Option ℤ) (U : Finset (Fin n))
    (levels : Finset ℤ) (hlevels : weightLevels a U ⊆ levels) (i : ℤ) :
    (((U.filter fun e => ∃ j, a e = some j ∧ i < j).card) : ℝ) =
      ∑ j ∈ levels with i < j, ((U.filter fun e => a e = some j).card : ℝ) := by
  classical
  have hs := sum_weightGroups a U levels hlevels (fun j => if i < j then 1 else 0)
  rw [Finset.sum_filter]
  have hleft : (∑ j ∈ levels, (if i < j then 1 else 0) *
      ((U.filter fun e => a e = some j).card : ℝ)) =
      ∑ j ∈ levels, if i < j then ((U.filter fun e => a e = some j).card : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hleft] at hs
  rw [hs]
  have hcount : (((U.filter fun e => ∃ j, a e = some j ∧ i < j).card) : ℝ) =
      ∑ e ∈ U, if (∃ j, a e = some j ∧ i < j) then 1 else 0 := by simp
  rw [hcount]
  apply Finset.sum_congr rfl
  intro e _
  cases a e <;> simp

lemma weightLevels_mono (a : Fin n → Option ℤ) {U V : Finset (Fin n)} (h : U ⊆ V) :
    weightLevels a U ⊆ weightLevels a V := by
  intro i hi
  obtain ⟨e, he, hi⟩ := (mem_weightLevels a U i).1 hi
  exact (mem_weightLevels a V i).2 ⟨e, h he, hi⟩

end MatroidProphet

end OAI
