import Mathlib

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest

structure Forest where
  parent : ℕ → ℕ
  parent_lt : ∀ n, 2 ≤ n → parent n < n

namespace Forest
variable (F : Forest)

def lineage (F : Forest) (n : ℕ) : List ℕ :=
  if _h : n < 2 then [n] else n :: F.lineage (F.parent n)
termination_by n
decreasing_by exact F.parent_lt n (by omega)

lemma lineage_base {n : ℕ} (h : n < 2) : F.lineage n = [n] := by
  rw [lineage, dite_eq_left h]

lemma lineage_step {n : ℕ} (h : 2 ≤ n) : F.lineage n = n :: F.lineage (F.parent n) := by
  rw [lineage, dite_eq_right (by omega : ¬n<2)]

lemma self_mem_lineage (n : ℕ) : n ∈ F.lineage n := by
  rw [lineage]
  split_ifs <;> simp

lemma mem_lineage_le {a n : ℕ} (h : a ∈ F.lineage n) : a ≤ n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a = n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      exact he.le
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · exact le_rfl
      · exact (ih (F.parent n) (F.parent_lt n (by omega)) h).trans
          (F.parent_lt n (by omega)).le

lemma lineage_nodup (n : ℕ) : (F.lineage n).Nodup := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · simp [F.lineage_base hn]
    · rw [F.lineage_step (by omega : 2 ≤ n),List.nodup_cons]
      have hlt := F.parent_lt n (by omega)
      exact ⟨fun h => (Nat.not_le_of_gt hlt) (F.mem_lineage_le h),ih _ hlt⟩

def root (F : Forest) (n : ℕ) : ℕ :=
  if _h : n < 2 then n else F.root (F.parent n)
termination_by n
decreasing_by exact F.parent_lt n (by omega)

lemma root_base {n : ℕ} (h : n < 2) : F.root n = n := by
  rw [root, dite_eq_left h]

lemma root_step {n : ℕ} (h : 2 ≤ n) : F.root n = F.root (F.parent n) := by
  rw [root, dite_eq_right (by omega : ¬n<2)]

lemma root_lt_two (n : ℕ) : F.root n < 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · simpa only [F.root_base hn] using hn
    · rw [F.root_step (by omega : 2 ≤ n)]
      exact ih _ (F.parent_lt n (by omega))

lemma root_mem_lineage (n : ℕ) : F.root n ∈ F.lineage n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · simp [F.root_base hn,F.lineage_base hn]
    · rw [F.root_step (by omega : 2 ≤ n),F.lineage_step (by omega : 2 ≤ n)]
      exact List.mem_cons_of_mem _ (ih _ (F.parent_lt n (by omega)))

lemma root_eq_of_mem {a n : ℕ} (h : a ∈ F.lineage n) : F.root a = F.root n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a=n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      rw [he]
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · rfl
      · rw [F.root_step (by omega : 2 ≤ n)]
        exact ih _ (F.parent_lt n (by omega)) h

lemma lineage_disjoint {a b : ℕ} (h : F.root a ≠ F.root b) :
    List.Disjoint (F.lineage a) (F.lineage b) := by
  intro n ha hb
  exact h ((F.root_eq_of_mem ha).symm.trans (F.root_eq_of_mem hb))

lemma lineage_subset_of_mem {a n : ℕ} (h : a ∈ F.lineage n) :
    F.lineage a ⊆ F.lineage n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a=n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      rw [he]
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · exact List.Subset.refl _
      · intro b hb
        rw [F.lineage_step (by omega : 2 ≤ n)]
        exact List.mem_cons_of_mem _ (ih _ (F.parent_lt n (by omega)) h hb)

lemma parent_mem_lineage {a n : ℕ} (ha : 2 ≤ a) (h : a ∈ F.lineage n) :
    F.parent a ∈ F.lineage n := by
  apply F.lineage_subset_of_mem h
  rw [F.lineage_step ha]
  exact List.mem_cons_of_mem _ (F.self_mem_lineage _)

lemma parent_injective_lineage {n a b : ℕ} (ha : a ∈ F.lineage n)
    (hb : b ∈ F.lineage n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (he : F.parent a = F.parent b) : a=b := by
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n < 2
    · have := F.mem_lineage_le ha
      omega
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at ha hb
      rcases ha with rfl|ha <;> rcases hb with rfl|hb
      · rfl
      · have hle := F.mem_lineage_le hb
        have hlt := F.parent_lt b hb2
        omega
      · have hle := F.mem_lineage_le ha
        have hlt := F.parent_lt a ha2
        omega
      · exact ih _ (F.parent_lt n (by omega)) ha hb ha2 hb2 he

lemma parent_injective_two_lineages {u v a b : ℕ}
    (huv : F.root u ≠ F.root v)
    (ha : a ∈ F.lineage u ∨ a ∈ F.lineage v)
    (hb : b ∈ F.lineage u ∨ b ∈ F.lineage v)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (he : F.parent a = F.parent b) : a=b := by
  rcases ha with ha|ha <;> rcases hb with hb|hb
  · exact F.parent_injective_lineage ha hb ha2 hb2 he
  · have h1 := F.root_eq_of_mem (F.parent_mem_lineage ha2 ha)
    have h2 := F.root_eq_of_mem (F.parent_mem_lineage hb2 hb)
    exact (huv (h1.symm.trans ((congrArg F.root he).trans h2))).elim
  · have h1 := F.root_eq_of_mem (F.parent_mem_lineage ha2 ha)
    have h2 := F.root_eq_of_mem (F.parent_mem_lineage hb2 hb)
    exact (huv (h2.symm.trans ((congrArg F.root he).symm.trans h1))).elim
  · exact F.parent_injective_lineage ha hb ha2 hb2 he

end Forest
end CriticalPercolation.InterpolationForest

namespace CriticalPercolation.InterpolationForest.Forest
open scoped Classical

variable (F : Forest)

def active (u v : ℕ) : Finset ℕ :=
  ((F.lineage u ++ F.lineage v).toFinset).filter (fun i => 2 ≤ i)

lemma mem_active {u v a : ℕ} : a ∈ F.active u v ↔
    (a ∈ F.lineage u ∨ a ∈ F.lineage v) ∧ 2 ≤ a := by
  simp [active]

lemma active_parent {u v a : ℕ} (ha : a ∈ F.active u v) :
    F.parent a < 2 ∨ F.parent a ∈ F.active u v := by
  by_cases hp : F.parent a < 2
  · exact Or.inl hp
  · apply Or.inr
    rw [mem_active] at ha ⊢
    exact ⟨ha.1.imp (F.parent_mem_lineage ha.2) (F.parent_mem_lineage ha.2),by omega⟩

lemma parent_injOn_active {u v : ℕ} (huv : F.root u ≠ F.root v) :
    Set.InjOn F.parent (↑(F.active u v) : Set ℕ) := by
  intro a ha b hb he
  rw [Finset.mem_coe,mem_active] at ha hb
  exact F.parent_injective_two_lineages huv ha.1 hb.1 ha.2 hb.2 he

theorem active_pair_multiplicity {u v : ℕ} (huv : F.root u ≠ F.root v) (a : ℕ) :
    ((F.active u v).filter fun b => b=a ∨ F.parent b=a).card ≤ 2 := by
  have h1 : ((F.active u v).filter fun b => b=a).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro b hb c hc
    exact (Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hc).2.symm
  have h2 : ((F.active u v).filter fun b => F.parent b=a).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro b hb c hc
    exact F.parent_injOn_active huv (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hc).1
      ((Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hc).2.symm)
  rw [Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (by omega)

lemma previous_lineage_le_parent {n a b : ℕ} (ha : a ∈ F.lineage n)
    (hb : b ∈ F.lineage n) (ha2 : 2 ≤ a) (hba : b < a) : b ≤ F.parent a := by
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n < 2
    · have := F.mem_lineage_le ha
      omega
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at ha hb
      rcases ha with rfl|ha <;> rcases hb with rfl|hb
      · omega
      · exact F.mem_lineage_le hb
      · have := F.mem_lineage_le ha
        have := F.parent_lt b (by omega : 2 ≤ b)
        omega
      · exact ih _ (F.parent_lt n (by omega)) ha hb ha2 hba

theorem previous_active_le_parent {u v a b : ℕ} (huv : F.root u ≠ F.root v)
    (ha : a ∈ F.active u v) (hb : b ∈ F.active u v)
    (hside : F.root a = F.root b) (hba : b < a) : b ≤ F.parent a := by
  rw [mem_active] at ha hb
  rcases ha.1 with hau|hav <;> rcases hb.1 with hbu|hbv
  · exact F.previous_lineage_le_parent hau hbu ha.2 hba
  · exact (huv ((F.root_eq_of_mem hau).symm.trans (hside.trans (F.root_eq_of_mem hbv)))).elim
  · exact (huv ((F.root_eq_of_mem hbu).symm.trans (hside.symm.trans (F.root_eq_of_mem hav)))).elim
  · exact F.previous_lineage_le_parent hav hbv ha.2 hba

end CriticalPercolation.InterpolationForest.Forest
end
end

end OAI
