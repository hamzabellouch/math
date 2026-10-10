import OAI.Combinatorics.CycleDecomposition.BatchIndexing

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai
noncomputable section
open Finset

theorem prefix_selection (S : ℕ → ℝ) (hS : ∀ j, 0 ≤ S j) (K N : ℕ)
    (hsupp : ∀ j, N ≤ j → S j = 0) (hne : ∃ j, 0 < S j) :
    ∃ i, 0 < S i ∧ ∑ j ∈ range (i+K+1), S j ≤ 4*(K+1:ℝ)*S i := by
  let A := (range N).filter (fun j => 0 < S j)
  have hA : A.Nonempty := by
    obtain ⟨j,hj⟩ := hne
    exact ⟨j, by
      simp only [A, mem_filter, mem_range]
      exact ⟨by by_contra hn; rw [hsupp j (by omega)] at hj; linarith, hj⟩⟩
  let i₀ := A.min' hA
  have hi₀A : i₀ ∈ A := A.min'_mem hA
  have hi₀pos : 0 < S i₀ := (mem_filter.mp hi₀A).2
  have hstart : (∑ j ∈ range (i₀+1), S j) = S i₀ := by
    apply sum_eq_single i₀
    · intro j hj hji
      by_contra hjzero
      have hjpos : 0 < S j := lt_of_le_of_ne (hS j) (Ne.symm hjzero)
      have hjA : j ∈ A := by
        simp only [A, mem_filter, mem_range]
        refine ⟨?_, hjpos⟩
        have hiN := (mem_range.mp (mem_filter.mp hi₀A).1)
        have hjle := mem_range.mp hj
        omega
      have hmin : i₀ ≤ j := A.min'_le j hjA
      have hjle := mem_range.mp hj
      omega
    · intro hi
      exact (hi (by simp)).elim
  let B := A.filter (fun i => (∑ j ∈ range (i+1), S j) ≤ 2*(K+1:ℝ)*S i)
  have hB : B.Nonempty := by
    refine ⟨i₀, mem_filter.mpr ⟨hi₀A, ?_⟩⟩
    rw [hstart]
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  let i := B.max' hB
  have hiB : i ∈ B := B.max'_mem hB
  have hiA : i ∈ A := (mem_filter.mp hiB).1
  have hipos : 0 < S i := (mem_filter.mp hiA).2
  have hinv : (∑ j ∈ range (i+1), S j) ≤ 2*(K+1:ℝ)*S i := (mem_filter.mp hiB).2
  refine ⟨i, hipos, ?_⟩
  by_contra hfail
  have hfail' : 4*(K+1:ℝ)*S i < ∑ j ∈ range (i+K+1), S j := lt_of_not_ge hfail
  have hwindow : 2*(K+1:ℝ)*S i < ∑ j ∈ Ico (i+1) (i+K+1), S j := by
    have hsplit := Finset.sum_range_add_sum_Ico S (by omega : i+1 ≤ i+K+1)
    linarith
  have hwindow_nonempty : (Ico (i+1) (i+K+1)).Nonempty := by
    by_contra hh
    rw [Finset.not_nonempty_iff_eq_empty.mp hh] at hwindow
    simp only [sum_empty] at hwindow
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  obtain ⟨j,hjw,hmax⟩ := Finset.exists_max_image (Ico (i+1) (i+K+1)) S hwindow_nonempty
  have hsum : (∑ l ∈ Ico (i+1) (i+K+1), S l) ≤ (K:ℝ)*S j := by
    calc
      _ ≤ ∑ _l ∈ Ico (i+1) (i+K+1), S j := sum_le_sum hmax
      _ = _ := by simp []
  have hdouble : 2*S i < S j := by
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hjpos : 0 < S j := by linarith
  have hjA : j ∈ A := by
    simp only [A, mem_filter, mem_range]
    exact ⟨by by_contra hjN; rw [hsupp j (by omega)] at hjpos; linarith, hjpos⟩
  have hjbounds := Finset.mem_Ico.mp hjw
  have hpartial : (∑ l ∈ Ico (i+1) (j+1), S l) ≤ (K:ℝ)*S j := by
    calc
      _ ≤ ∑ l ∈ Ico (i+1) (i+K+1), S l := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro l hl
          simp only [mem_Ico] at hl ⊢
          omega
        · intro l _ _; exact hS l
      _ ≤ _ := hsum
  have hjinv : (∑ l ∈ range (j+1), S l) ≤ 2*(K+1:ℝ)*S j := by
    have hsplit := Finset.sum_range_add_sum_Ico S (by omega : i+1 ≤ j+1)
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hjB : j ∈ B := mem_filter.mpr ⟨hjA,hjinv⟩
  have hji : j ≤ i := B.le_max' j hjB
  omega

end
end ErdosGallai

end

namespace ErdosGallai

def MainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∃ k : ℕ, EdgeDecomposition G k ∧ (k : ℝ) ≤ C * n
end ErdosGallai
end
end

end OAI
