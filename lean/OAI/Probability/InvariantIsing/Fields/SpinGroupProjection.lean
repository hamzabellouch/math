import OAI.Probability.InvariantIsing.Fields.SpinGroupSlice
import OAI.Probability.InvariantIsing.Fields.SpinSliceProjection

namespace OAI

/-! A nearest projection to all group constraints at once. Its number of
changed spins is exactly the sum of the group count discrepancies. -/

noncomputable section
open scoped BigOperators symmDiff

namespace InvariantIsing

lemma exists_subset_card_nearest {I : Type*} [DecidableEq I] (A S : Finset I)
    (hAS : A ⊆ S) (k : ℕ) (hk : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧ (A ∆ T).card = A.card - k + (k - A.card) := by
  by_cases hka : k ≤ A.card
  · obtain ⟨T, hTA, hT⟩ := Finset.exists_subset_card_eq hka
    refine ⟨T, hTA.trans hAS, hT, ?_⟩
    rw [Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr hTA,
      Finset.union_empty, Finset.card_sdiff_of_subset hTA, hT, Nat.sub_eq_zero_of_le hka,
      Nat.add_zero]
  · have hak : A.card ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hka)
    have hrem : k - A.card ≤ (S \ A).card := by
      rw [Finset.card_sdiff_of_subset hAS]
      omega
    obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq hrem
    have hd : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      exact (Finset.mem_sdiff.mp (hB hiB)).2 hiA
    have hT : (A ∪ B).card = k := by
      rw [Finset.card_union_of_disjoint hd, hBc]
      omega
    refine ⟨A ∪ B, Finset.union_subset hAS (hB.trans Finset.sdiff_subset), hT, ?_⟩
    rw [Finset.symmDiff_def,
      Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_left,
      Finset.empty_union, Finset.card_sdiff_of_subset Finset.subset_union_left, hT,
      Nat.sub_eq_zero_of_le hak, Nat.zero_add]

lemma exists_spin_group_projection {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) (σ : Spin N) :
    ∃ τ ∈ spinGroupSlice group k,
      hammingDist σ τ = ∑ a, ((spinGroupCount group σ a - k a) +
        (k a - spinGroupCount group σ a)) := by
  classical
  let S := fun a => Finset.univ.filter (fun i => group i = a)
  let P := fun a => Finset.univ.filter (fun i => group i = a ∧ σ i = true)
  have hPS (a : A) : P a ⊆ S a := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩
  choose T hT hcard hdist using fun a => exists_subset_card_nearest (P a) (S a) (hPS a) (k a) (hk a)
  let τ : Spin N := fun i => decide (i ∈ T (group i))
  have hTa {a : A} {i : Fin N} (hi : i ∈ T a) : group i = a :=
    (Finset.mem_filter.mp (hT a hi)).2
  have hcount (a : A) : spinGroupCount group τ a = k a := by
    have he : (Finset.univ.filter fun i => group i = a ∧ τ i = true) = T a := by
      ext i
      by_cases hi : group i = a
      · simp [τ, hi]
      · have hn : i ∉ T a := fun hm => hi (hTa hm)
        simp [hi, hn]
    exact (congrArg Finset.card he).trans (hcard a)
  refine ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcount⟩, ?_⟩
  let D := Finset.univ.filter (fun i => σ i ≠ τ i)
  have he (a : A) : D.filter (fun i => group i = a) = P a ∆ T a := by
    ext i
    by_cases hi : group i = a
    · cases hσ : σ i <;> simp [D, P, τ, hi, hσ, Finset.mem_symmDiff]
    · have hn : i ∉ T a := fun hm => hi (hTa hm)
      simp [D, P, hi, hn, Finset.mem_symmDiff]
  change D.card = _
  rw [Finset.card_eq_sum_card_fiberwise (s := D) (t := Finset.univ)
    (f := group) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro a _
  rw [he, hdist]
  rfl

def spinGroupProjection {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (σ : Spin N) : Spin N := Classical.choose (exists_spin_group_projection group k hk σ)

lemma spinGroupProjection_mem {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) (σ : Spin N) :
    spinGroupProjection group k hk σ ∈ spinGroupSlice group k :=
  (Classical.choose_spec (exists_spin_group_projection group k hk σ)).1

lemma spinGroupProjection_distance {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) (σ : Spin N) :
    hammingDist σ (spinGroupProjection group k hk σ) =
      ∑ a, ((spinGroupCount group σ a - k a) + (k a - spinGroupCount group σ a)) :=
  (Classical.choose_spec (exists_spin_group_projection group k hk σ)).2

end InvariantIsing

end

end OAI
