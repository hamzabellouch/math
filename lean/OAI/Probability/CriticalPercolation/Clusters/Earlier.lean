import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ComponentSelf

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V : Type*} {n : ℕ}

def earlier (x : Fin n → V) (k : Fin n) : Set V := {v | ∃ j < k, x j = v}
def first (H : SimpleGraph V) (x : Fin n → V) (k : Fin n) : Prop :=
  x k ∉ roots H (earlier x k)
noncomputable def select (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) : ℝ :=
  if first H x k ∧ x i ∈ component H (x k) then 1 else 0

lemma root_not_mem_earlier {x : Fin n → V} (hx : Function.Injective x) (k : Fin n) :
    x k ∉ earlier x k := by
  rintro ⟨j, hj, heq⟩
  exact (ne_of_lt hj) (hx heq)

lemma earlier_mono (x : Fin n → V) {k l : Fin n} (hkl : k ≤ l) :
    earlier x k ⊆ earlier x l := by
  rintro v ⟨j, hj, rfl⟩
  exact ⟨j, hj.trans_le hkl, rfl⟩

lemma first_unique {H : SimpleGraph V} {x : Fin n → V} {k l i : Fin n}
    (hk : first H x k) (hki : x i ∈ component H (x k))
    (hl : first H x l) (hli : x i ∈ component H (x l)) : k = l := by
  apply le_antisymm
  · by_contra! h
    exact hk ⟨x l, ⟨l, h, rfl⟩, hli.trans hki.symm⟩
  · by_contra! h
    exact hl ⟨x k, ⟨k, h, rfl⟩, hki.trans hli.symm⟩

lemma exists_first (H : SimpleGraph V) (x : Fin n → V) (i : Fin n) :
    ∃ k, first H x k ∧ x i ∈ component H (x k) := by
  classical
  let J := Finset.univ.filter (fun j => x i ∈ component H (x j))
  have hi : i ∈ J := by simp [J, component_self]
  have hJ : J.Nonempty := ⟨i, hi⟩
  let k := J.min' hJ
  have hkJ : k ∈ J := Finset.min'_mem J hJ
  have hki : x i ∈ component H (x k) := (Finset.mem_filter.mp hkJ).2
  refine ⟨k, ?_, hki⟩
  rintro ⟨v, ⟨j, hj, rfl⟩, hjk⟩
  have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjk.trans hki⟩
  have hkj : k ≤ j := Finset.min'_le J j hjJ
  exact (not_lt_of_ge hkj) hj

lemma select_nonneg (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) :
    0 ≤ select H x k i := by unfold select; positivity

lemma select_zero_of_lt (H : SimpleGraph V) (x : Fin n → V) {k i : Fin n} (hik : i < k) :
    select H x k i = 0 := by
  apply ite_eq_right
  rintro ⟨hk, hki⟩
  exact hk ⟨x i, ⟨i, hik, rfl⟩, hki.symm⟩

lemma select_diag (H : SimpleGraph V) (x : Fin n → V) (k : Fin n) :
    select H x k k = if first H x k then 1 else 0 := by
  simp only [select, component_self, and_true]

lemma select_mul_sum (H : SimpleGraph V) (x : Fin n → V) (i : Fin n)
    (a : Fin n → ℝ) {k : Fin n} (hk : first H x k)
    (hki : x i ∈ component H (x k)) :
    ∑ l, select H x l i * a l = a k := by
  classical
  rw [Finset.sum_eq_single k]
  · simp [select, hk, hki]
  · intro l _ hlk
    have hh : ¬ (first H x l ∧ x i ∈ component H (x l)) := by
      rintro ⟨hl, hli⟩
      exact hlk (first_unique hl hli hk hki)
    simp [select, hh]
  · simp

lemma select_mass (H : SimpleGraph V) (x : Fin n → V) (i : Fin n) :
    ∑ k, select H x k i = 1 := by
  obtain ⟨k, hk, hki⟩ := exists_first H x i
  simpa using select_mul_sum H x i (fun _ => 1) hk hki

lemma cluster_partition (H : SimpleGraph V) (x : Fin n → V)
    (F : Set V → ℝ) (i : Fin n) :
    F (component H (x i)) = ∑ k, select H x k i * F (component H (x k)) := by
  obtain ⟨k, hk, hki⟩ := exists_first H x i
  rw [select_mul_sum H x i _ hk hki, component_eq_of_mem hki]

lemma first_hit_not_mem_roots_iff (H : SimpleGraph V) (x : Fin n → V)
    {j i : Fin n} (hj : first H x j) (hji : x i ∈ component H (x j)) (k : Fin n) :
    x i ∉ roots H (earlier x k) ↔ k ≤ j := by
  constructor
  · intro hi
    by_contra! hjk
    exact hi ⟨x j, ⟨j, hjk, rfl⟩, hji⟩
  · rintro hkj ⟨v, ⟨l, hlk, rfl⟩, hli⟩
    exact hj ⟨x l, ⟨l, hlk.trans_le hkj, rfl⟩, hli.trans hji.symm⟩

lemma select_truncation (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) :
    (if x i ∉ roots H (earlier x k) then (1 : ℝ) else 0) =
      select H x k i + ∑ l, if k < l then select H x l i else 0 := by
  classical
  obtain ⟨j, hj, hji⟩ := exists_first H x i
  have he : ∀ l, select H x l i = if l = j then 1 else 0 := by
    intro l
    by_cases hlj : l = j
    · subst l
      simp [select, hj, hji]
    · have hh : ¬ (first H x l ∧ x i ∈ component H (x l)) := by
        rintro ⟨hl, hli⟩
        exact hlj (first_unique hl hli hj hji)
      simp [select, hh, hlj]
  simp_rw [he]
  have hsum : (∑ l : Fin n, if k < l then if l = j then (1 : ℝ) else 0 else 0) =
      if k < j then 1 else 0 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hlj
      simp [hlj]
    · simp
  rw [hsum]
  simp only [first_hit_not_mem_roots_iff H x hj hji k]
  rcases lt_trichotomy k j with h | h | h
  · simp [h, ne_of_lt h, le_of_lt h]
  · subst j
    simp
  · simp [ne_of_gt h, not_le_of_gt h, not_lt_of_gt h]

end CriticalPercolation.ClusterColumns

end
end

end OAI
