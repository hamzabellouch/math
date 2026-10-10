import OAI.Probability.MatroidProphet.RankAccounting

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset

variable {α : Type*} [Fintype α]

def oldPrefix (b : ℕ → α) (k : ℕ) : Set α := {x | ∃ i < k, b i = x}

@[simp] lemma oldPrefix_zero
    {α : Type u_1} [Fintype α] (b : ℕ → α) : oldPrefix b 0 = ∅ := by
  ext x
  simp [oldPrefix]

lemma oldPrefix_succ
    {α : Type u_1} [Fintype α] (b : ℕ → α) (k : ℕ) :
    oldPrefix b (k + 1) = insert (b k) (oldPrefix b k) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inr ⟨i, hi, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨k, Nat.lt_succ_self k, rfl⟩
    · exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), rfl⟩

lemma oldPrefix_mono
    {α : Type u_1} [Fintype α] (b : ℕ → α) : Monotone (oldPrefix b) := by
  intro j k hjk x hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, lt_of_lt_of_le hi hjk, rfl⟩

lemma conditionalRank_singleton_of_notMem_closure (M : Matroid α)
    (P : Set α) {e : α} (he : e ∈ M.E) (hne : e ∉ M.closure P) :
    conditionalRank M {e} P = 1 := by
  unfold conditionalRank natRank
  rw [Set.singleton_union, M.eRk_insert_eq_add_one ⟨he, hne⟩,
    ENat.toNat_add (rank_ne_top M P) (by simp)]
  simp

lemma conditionalRank_singleton_of_mem_closure
    {α : Type u_1} [Fintype α] (M : Matroid α)
    (P : Set α) {e : α} (he : e ∈ M.closure P) :
    conditionalRank M {e} P = 0 := by
  have h := congrArg (natRank M) (M.closure_insert_eq_of_mem_closure he)
  simp only [natRank_closure] at h
  simp only [conditionalRank, Set.singleton_union, h, Nat.sub_self]

noncomputable def omittable (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range r).filter (fun k => b k ∈ M.closure (oldPrefix b k ∪ A))

lemma omittable_drop (M : Matroid α) (b : ℕ → α) (A : Set α) (k : ℕ)
    (he : b k ∈ M.E) (hind : b k ∉ M.closure (oldPrefix b k))
    (homit : b k ∈ M.closure (oldPrefix b k ∪ A)) :
    conditionalRank M A (oldPrefix b (k + 1)) + 1 =
      conditionalRank M A (oldPrefix b k) := by
  have hex := conditionalRank_exchange M {b k} A (oldPrefix b k)
  rw [conditionalRank_singleton_of_notMem_closure M _ he hind,
    conditionalRank_singleton_of_mem_closure M _ homit] at hex
  rw [oldPrefix_succ, Set.union_singleton] at *
  omega

lemma card_omittable_le_rank (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ)
    (he : ∀ k < r, b k ∈ M.E)
    (hind : ∀ k < r, b k ∉ M.closure (oldPrefix b k)) :
    (omittable M b A r).card ≤ natRank M A := by
  classical
  let p := fun k => conditionalRank M A (oldPrefix b k)
  have hp : ∀ k < r, p (k + 1) ≤ p k := by
    intro k _
    exact conditionalRank_antitone M A (oldPrefix_mono b (Nat.le_succ k))
  have hdrop := sum_potential_drop_le p r hp
  have hsum : (omittable M b A r).card ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
    rw [Finset.card_eq_sum_ones]
    calc
      (∑ k ∈ omittable M b A r, 1) ≤
          ∑ k ∈ omittable M b A r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_filter.mp hk
        have hkr := Finset.mem_range.mp hk'.1
        have hd := omittable_drop M b A k (he k hkr) (hind k hkr) hk'.2
        change p (k + 1) + 1 = p k at hd
        omega
      _ ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro _ _ _
          exact Nat.zero_le _
  have hzero : p 0 = natRank M A := by simp [p, conditionalRank]
  omega

lemma notMem_closure_before_nonomittable
    {α : Type u_1} [Fintype α] (M : Matroid α) (b : ℕ → α)
    (A P : Set α) (r k : ℕ) (hk : k < r)
    (hkeep : k ∉ omittable M b A r) (hP : P ⊆ oldPrefix b k ∪ A) :
    b k ∉ M.closure P := by
  classical
  intro he
  apply hkeep
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,
    M.closure_subset_closure hP he⟩

noncomputable def vulnerable (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range r).filter (fun k =>
    b k ∉ M.closure (oldPrefix b k) ∧ b k ∈ M.closure (oldPrefix b k ∪ A))

lemma card_vulnerable_le_rank (M : Matroid α) (b : ℕ → α) (A : Set α) (r : ℕ)
    (he : ∀ k < r, b k ∈ M.E) :
    (vulnerable M b A r).card ≤ natRank M A := by
  classical
  let p := fun k => conditionalRank M A (oldPrefix b k)
  have hp : ∀ k < r, p (k + 1) ≤ p k := by
    intro k _
    exact conditionalRank_antitone M A (oldPrefix_mono b (Nat.le_succ k))
  have hdrop := sum_potential_drop_le p r hp
  have hsum : (vulnerable M b A r).card ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
    rw [Finset.card_eq_sum_ones]
    calc
      (∑ k ∈ vulnerable M b A r, 1) ≤
          ∑ k ∈ vulnerable M b A r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_filter.mp hk
        have hkr := Finset.mem_range.mp hk'.1
        have hd := omittable_drop M b A k (he k hkr) hk'.2.1 hk'.2.2
        change p (k + 1) + 1 = p k at hd
        omega
      _ ≤ ∑ k ∈ range r, (p k - p (k + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro _ _ _
          exact Nat.zero_le _
  have hzero : p 0 = natRank M A := by simp [p, conditionalRank]
  omega

end Pivots
end MatroidProphet

end OAI
