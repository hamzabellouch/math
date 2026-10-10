import OAI.Analysis.Laughlin.Fock.Perturbation

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators InnerProductSpace

noncomputable def occupationQuadratic {I : Type*} [Fintype I]
    (Q : ℕ) (R : I → I → ℝ) (v : I → Space Q) : ℝ :=
  (∑ i, ∑ j, (R i j : ℂ) * occupationInner Q (v i) (v j)).re

theorem occupationQuadratic_coordinates {I : Type*} [Fintype I]
    (Q : ℕ) (R : I → I → ℝ) (v : I → Space Q) :
    occupationQuadratic Q R v = ∑ A : Finset (Fin (Q+1)), ∑ i, ∑ j,
      R i j * ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ := by
  simp only [occupationQuadratic,occupationInner,Finset.mul_sum,Complex.re_sum,
    Complex.inner,Complex.star_def]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro A hA
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem truncatedQuadratic_error {I : Type*} [Fintype I] (L Q : ℕ)
    (R S : I → I → ℝ) (v : I → Space Q) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ A : Finset (Fin (Q+1)), ∀ i j,
      |((truncatedDiagonals L Q A)⁻¹)^2 * R i j - S i j| ≤ ε) :
    |occupationQuadratic Q R (fun i => truncatedScalingInv L Q (v i)) - occupationQuadratic Q S v| ≤
      ε * (Fintype.card I : ℝ) * ∑ i, occupationNormSq Q (v i) := by
  have he : occupationQuadratic Q R (fun i => truncatedScalingInv L Q (v i)) - occupationQuadratic Q S v =
      ∑ A : Finset (Fin (Q+1)), ∑ i, ∑ j,
        (((truncatedDiagonals L Q A)⁻¹)^2 * R i j - S i j) *
          ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ := by
    rw [occupationQuadratic_coordinates,occupationQuadratic_coordinates,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro A hA
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j hj
    rw [truncatedScalingInv_coordinate,truncatedScalingInv_coordinate]
    simp only [Complex.inner,map_mul,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    ring
  rw [he]
  exact occupation_coefficient_perturbation Q _ v ε hε hR

end Laughlin.Fock

end OAI
