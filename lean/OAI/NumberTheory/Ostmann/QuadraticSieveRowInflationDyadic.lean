import OAI.NumberTheory.Ostmann.QuadraticSieveRowInflation

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem quadraticNorm_le_sum_cover (V S J : Finset ℕ) (W : ℕ → Finset ℕ)
    (hcover : ∀ v ∈ V, ∃ j ∈ J, v ∈ W j) :
    quadraticNorm V S ≤ ∑ j ∈ J, quadraticNorm (W j) S := by
  classical
  apply quadraticNorm_le_of_bound V S
    (Finset.sum_nonneg (fun j hj => quadraticNorm_nonneg (W j) S))
  intro a
  let f : ℕ → ℝ := fun v => ‖∑ n ∈ S, a n*(jacobiSym (n:ℤ) v:ℂ)‖^2
  have hf (v : ℕ) : 0 ≤ f v := sq_nonneg _
  have h1 : (∑ v ∈ V, f v) ≤ ∑ v ∈ V, ∑ j ∈ J, if v ∈ W j then f v else 0 := by
    apply Finset.sum_le_sum
    intro v hv
    obtain ⟨j,hj,hvW⟩ := hcover v hv
    have hh := Finset.single_le_sum
      (fun i hi => show 0 ≤ (if v ∈ W i then f v else 0) by split_ifs <;> positivity) hj
    simpa only [ite_eq_left hvW] using hh
  have h2 : (∑ v ∈ V, ∑ j ∈ J, if v ∈ W j then f v else 0) ≤
      ∑ j ∈ J, jacobiEnergy (W j) S a := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j hj
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (show V.filter (fun v => v ∈ W j) ⊆ W j from fun v hv => (Finset.mem_filter.mp hv).2)
    intro v hv hnot
    exact hf v
  have h3 : (∑ j ∈ J, jacobiEnergy (W j) S a) ≤
      (∑ j ∈ J, quadraticNorm (W j) S)*coefficientEnergy S a := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j hj => jacobiEnergy_le_quadraticNorm (W j) S a)
  exact (h1.trans h2).trans h3

theorem exists_rowInflationTarget_dyadic (M R : ℕ) (S : Finset ℕ) :
    ∃ j : ℕ, j < 5 ∧ quadraticNorm (rowInflationTarget M R) S ≤
      5*quadraticNorm (dyadicSquarefreeRows (2^j*(R*M))) S := by
  classical
  have hcover := quadraticNorm_le_sum_cover (rowInflationTarget M R) S (Finset.range 5)
    (fun j => dyadicSquarefreeRows (2^j*(R*M))) (by
      intro v hv
      exact Finset.mem_biUnion.mp (rowInflationTarget_subset_dyadic_union M R hv))
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range 5)
    (fun j => quadraticNorm (dyadicSquarefreeRows (2^j*(R*M))) S) (by simp)
  refine ⟨j,Finset.mem_range.mp hj,hcover.trans ?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range 5, quadraticNorm (dyadicSquarefreeRows (2^j*(R*M))) S :=
      Finset.sum_le_sum (fun i hi => hmax i hi)
    _ = _ := by simp

theorem exists_quadraticNorm_rowInflation_dyadic :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (M N R : ℕ), 0 < M → 0 < N →
      C*Real.log (2*(M:ℝ)*N) ≤ R → ∀ S : Finset ℕ,
      S ⊆ oddSquarefreeUpTo N → ∃ j : ℕ, j < 5 ∧
      quadraticNorm (dyadicSquarefreeRows M) S ≤
        20*quadraticNorm (dyadicSquarefreeRows (2^j*(R*M))) S := by
  obtain ⟨C,hC,hbound⟩ := exists_quadraticNorm_rowInflation
  refine ⟨C,hC,?_⟩
  intro M N R hM hN hR S hS
  obtain ⟨j,hj,hjbound⟩ := exists_rowInflationTarget_dyadic M R S
  refine ⟨j,hj,?_⟩
  have hh := hbound M N R hM hN hR S hS
  linarith

end Ostmann.QuadraticSieve

end

end OAI
