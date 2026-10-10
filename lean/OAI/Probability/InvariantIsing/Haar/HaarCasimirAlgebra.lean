import OAI.Probability.InvariantIsing.Haar.HaarPlaneAdjoint

namespace OAI

/-! Adjoint invariance of the quadratic orthogonal Casimir in any representation. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma sum_skew_symmetric_coeff_swap {N : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A)
    (T : Fin N → Fin N → V) (hT : ∀ i j, T i j = T j i) :
    (∑ i, ∑ j, A j i • T i j) = 0 := by
  rw [Finset.sum_comm]
  exact sum_skew_symmetric_coeff A hA (fun i j => T j i) (fun i j => hT j i)

/-- The coefficient cancellation uses only skew symmetry, with no analytic premise. -/
theorem plane_adjoint_jordan_sum {N : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (F : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] Module.End ℝ V)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    (∑ i, ∑ j,
      (F (planeGenerator i j)*F (A*planeGenerator i j-planeGenerator i j*A)+
       F (A*planeGenerator i j-planeGenerator i j*A)*F (planeGenerator i j))) = 0 := by
  let x := fun i j => F (planeGenerator i j)
  have he (i j : Fin N) :
      F (planeGenerator i j)*F (A*planeGenerator i j-planeGenerator i j*A)+
        F (A*planeGenerator i j-planeGenerator i j*A)*F (planeGenerator i j) =
      (∑ k, A k i • (x i j*x k j+x k j*x i j))+
        ∑ k, A k j • (x i j*x i k+x i k*x i j) := by
    rw [planeGenerator_adjoint_expansion A hA i j,map_add,map_sum,map_sum]
    simp only [map_smul,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,
      smul_mul_assoc,mul_smul_comm,smul_add]
    dsimp only [x]
    simp only [Finset.sum_add_distrib]
    abel
  simp_rw [he,Finset.sum_add_distrib]
  have h₁ : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      A k i • (x i j*x k j+x k j*x i j)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    exact sum_skew_symmetric_coeff_swap A hA _ (fun i k => add_comm _ _)
  have h₂ : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      A k j • (x i j*x i k+x i k*x i j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact sum_skew_symmetric_coeff_swap A hA _ (fun j k => add_comm _ _)
  rw [h₁,h₂,zero_add]

end InvariantIsing

end

end OAI
