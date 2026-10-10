import OAI.Analysis.Laughlin.Operators.PositiveFockLift

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix

theorem occupation_matrix_quadratic_positive {I : Type*} [Fintype I]
    (Q : ℕ) (M : Matrix I I ℂ) (hM : M.PosSemidef) (v : I → Space Q) :
    0 ≤ (∑ i, ∑ j, M i j * occupationInner Q (v i) (v j)).re := by
  have he : (∑ i, ∑ j, M i j * occupationInner Q (v i) (v j)) =
      ∑ A : Finset (Fin (Q+1)), star (fun i => (occupationBasis Q).repr (v i) A) ⬝ᵥ
        (M*ᵥ (fun i => (occupationBasis Q).repr (v i) A)) := by
    simp only [occupationInner,dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro A hA
    ring
  rw [he,Complex.re_sum]
  exact Finset.sum_nonneg (fun A hA => (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg _)).1)

theorem occupation_matrix_quadratic_factor {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (W : Matrix J I ℂ) (C : Matrix I I ℂ) (v : J → Space Q) :
    (∑ i, ∑ j, C i j * occupationInner Q
      (∑ a, star (W a i) • v a) (∑ b, star (W b j) • v b)) =
      ∑ a, ∑ b, (W*C*Wᴴ) a b * occupationInner Q (v a) (v b) := by
  simp_rw [occupationInner_sum_left,occupationInner_smul_left,star_star,
    occupationInner_sum_right,occupationInner_smul_right]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a ha
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b hb
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring

end Laughlin.Fock

end OAI
