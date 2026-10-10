import OAI.Probability.InvariantIsing.Haar.HaarPlaneFrame

namespace OAI

/-! The sum of squared Lie brackets, with the precise dimension factor. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

def planeFunctionalMatrix {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ell (planeGenerator i j)

lemma planeFunctionalMatrix_skew {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ) :
    (planeFunctionalMatrix ell).transpose = -planeFunctionalMatrix ell := by
  ext i j
  change ell (planeGenerator j i) = -ell (planeGenerator i j)
  rw [planeGenerator_swap,map_neg]

lemma sum_plane_functional_bracket_sq {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ)
    (E : Matrix (Fin N) (Fin N) ℝ) (hE : E.transpose = -E) :
    (∑ i, ∑ j, (ell (E*planeGenerator i j-planeGenerator i j*E))^2) =
      matrixFrobeniusPair (E*planeFunctionalMatrix ell-planeFunctionalMatrix ell*E)
        (E*planeFunctionalMatrix ell-planeFunctionalMatrix ell*E) := by
  let A := planeFunctionalMatrix ell
  have hA : A.transpose = -A := planeFunctionalMatrix_skew ell
  have hs (i j : Fin N) :
      4*(ell (E*planeGenerator i j-planeGenerator i j*E))^2 =
        (matrixFrobeniusPair (E*A-A*E) (planeGenerator i j))^2 := by
    have hr := plane_functional_representation ell
      (E*planeGenerator i j-planeGenerator i j*E)
      (skew_matrix_bracket hE (planeGenerator_transpose i j))
    have hb := matrixFrobeniusPair_bracket E A (planeGenerator i j) hE
    change matrixFrobeniusPair A _ = _ at hr
    rw [hr] at hb
    rw [hb]
    ring
  have ht := sum_matrixFrobeniusPair_plane_sq (E*A-A*E) (skew_matrix_bracket hE hA)
  simp_rw [← hs] at ht
  simp only [← Finset.mul_sum] at ht
  change _ = matrixFrobeniusPair (E*A-A*E) (E*A-A*E)
  linarith

/-- The ordered-plane convention has curvature factor `N - 2`. The factor
four here becomes one after the antisymmetric Hessian estimate. -/
theorem sum_plane_functional_double_bracket_sq {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      (ell (planeGenerator i j*planeGenerator k l-
        planeGenerator k l*planeGenerator i j))^2) =
      (4*((N : ℝ)-2))*(∑ i, ∑ j, (ell (planeGenerator i j))^2) := by
  simp_rw [sum_plane_functional_bracket_sq ell _ (planeGenerator_transpose _ _)]
  rw [sum_planeGenerator_bracket_norm_sq _ (planeFunctionalMatrix_skew ell),
    matrixFrobeniusPair_self]
  rfl

end InvariantIsing

end

end OAI
