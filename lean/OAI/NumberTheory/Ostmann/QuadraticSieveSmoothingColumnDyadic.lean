import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothingColumnDyadicBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open scoped BigOperators

theorem smoothingEnergy_le_binary_sum (M K N : ℕ) (a : ℕ → ℂ) :
    smoothingEnergy M K (oddSquarefreeUpTo N) a ≤
      (Nat.log 2 N+1:ℕ)*
        ∑ j ∈ Finset.range (Nat.log 2 N+1), smoothingEnergy M K (binarySquarefreeRows N j) a := by
  unfold smoothingEnergy weightedNumeratorEnergy
  calc
    _ ≤ ∑ m ∈ smoothingRows M K, smoothingWeight M m *
        ((Nat.log 2 N+1:ℕ)*∑ j ∈ Finset.range (Nat.log 2 N+1),
          ‖∑ n ∈ binarySquarefreeRows N j,a n*(jacobiSym m n:ℂ)‖^2) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (smoothingWeight_nonneg M m)
      rw [sum_oddSquarefree_eq_dyadic]
      simpa only [Finset.card_range] using smoothing_column_cauchy
        (Finset.range (Nat.log 2 N+1))
        (fun j => ∑ n ∈ binarySquarefreeRows N j,a n*(jacobiSym m n:ℂ))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro m hm
      ring

theorem coefficientEnergy_binary_sum (N : ℕ) (a : ℕ → ℂ) :
    (∑ j ∈ Finset.range (Nat.log 2 N+1), coefficientEnergy (binarySquarefreeRows N j) a) =
      coefficientEnergy (oddSquarefreeUpTo N) a := by
  unfold coefficientEnergy
  exact (sum_oddSquarefree_eq_dyadic N _).symm

theorem exists_smoothingNorm_binary_control (M K N : ℕ) :
    ∃ j < Nat.log 2 N+1, smoothingNorm M K (oddSquarefreeUpTo N) ≤
      (Nat.log 2 N+1:ℕ)*smoothingNorm M K (binarySquarefreeRows N j) := by
  classical
  have hne : (Finset.range (Nat.log 2 N+1)).Nonempty := ⟨0,by simp⟩
  obtain ⟨j,hj,hmax⟩ := (Finset.range (Nat.log 2 N+1)).exists_max_image
    (fun j => smoothingNorm M K (binarySquarefreeRows N j)) hne
  refine ⟨j,Finset.mem_range.mp hj,?_⟩
  have hnorm := smoothingNorm_nonneg M K (binarySquarefreeRows N j)
  apply weightedNumeratorNorm_le_of_bound _ _ _ (by positivity)
  intro a
  calc
    _ ≤ (Nat.log 2 N+1:ℕ)*
        ∑ i ∈ Finset.range (Nat.log 2 N+1),smoothingEnergy M K (binarySquarefreeRows N i) a :=
      smoothingEnergy_le_binary_sum M K N a
    _ ≤ (Nat.log 2 N+1:ℕ)*
        ∑ i ∈ Finset.range (Nat.log 2 N+1),
          smoothingNorm M K (binarySquarefreeRows N j)*coefficientEnergy (binarySquarefreeRows N i) a := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      exact (smoothingEnergy_le_norm M K (binarySquarefreeRows N i) a).trans
        (mul_le_mul_of_nonneg_right (hmax i hi) (coefficientEnergy_nonneg _ _))
    _ = _ := by rw [← Finset.mul_sum,coefficientEnergy_binary_sum]; ring

end Ostmann.QuadraticSieve

end

end OAI
