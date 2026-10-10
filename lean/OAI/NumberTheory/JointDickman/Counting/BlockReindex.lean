import OAI.NumberTheory.JointDickman.Counting.BlockCounting

namespace OAI

/-! # Exact block averaging and reindexing into square matrices -/

namespace JointDickman
open Finset

theorem sum_lag_pairs (M : ℕ) (J : Finset ℤ) (K : ℤ → ℤ → ℝ) :
    (∑ j ∈ J, ∑ i ∈ blockOverlap M j, K j i) =
      ∑ i ∈ Icc 1 (M : ℤ), ∑ k ∈ Icc 1 (M : ℤ),
        if k-i ∈ J then K (k-i) i else 0 := by
  classical
  simp only [blockOverlap, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter, ← sum_filter]
  apply sum_bij (fun j _ => i+j)
  · intro j hj
    have h := mem_filter.mp hj
    exact mem_filter.mpr ⟨h.2,by simpa using h.1⟩
  · intro a _ b _ hab
    omega
  · intro k hk
    have h := mem_filter.mp hk
    refine ⟨k-i, mem_filter.mpr ⟨h.2,?_⟩,?_⟩
    · simpa only [add_sub_cancel] using h.1
    · simp
  · intro j _
    simp

noncomputable def finiteBlockAverage (M V : ℕ) (J : Finset ℤ)
    (K : ℤ → ℤ → ℝ) : ℝ :=
  (∑ s ∈ blockOrigins M V, ∑ j ∈ J, ∑ i ∈ blockOverlap M j,
    if s+i ∈ Icc 1 (V : ℤ) then K j (s+i) else 0)/(M : ℝ)

theorem finiteBlockAverage_eq (M V : ℕ) (hM : 0 < M)
    (J : Finset ℤ) (hJ : ∀ j ∈ J, j.natAbs ≤ M) (K : ℤ → ℤ → ℝ) :
    finiteBlockAverage M V J K =
      ∑ j ∈ J, (1-(j.natAbs : ℝ)/M)*(∑ n ∈ Icc 1 (V : ℤ), K j n) := by
  unfold finiteBlockAverage
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [sum_block_overlap M V j (hJ j hj), Nat.cast_sub (hJ j hj)]
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

theorem finiteBlockAverage_square (M V : ℕ) (J : Finset ℤ)
    (K : ℤ → ℤ → ℝ) :
    finiteBlockAverage M V J K =
      (∑ s ∈ blockOrigins M V, ∑ i ∈ Icc 1 (M : ℤ), ∑ k ∈ Icc 1 (M : ℤ),
        if k-i ∈ J ∧ s+i ∈ Icc 1 (V : ℤ) then K (k-i) (s+i) else 0)/(M : ℝ) := by
  unfold finiteBlockAverage
  congr 1
  apply sum_congr rfl
  intro s _
  rw [sum_lag_pairs]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro k _
  by_cases h : k-i ∈ J <;> simp [h]

end JointDickman

end OAI
