import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternModel

namespace OAI

/-! The real quadratic form in its actual orthonormal eigenvector coordinates. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma hermitian_quadratic_coordinates {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin N)) :
    ⟪x,A.toEuclideanLin x⟫ =
      ∑ i, hA.eigenvalues i*(hA.eigenvectorBasis.repr x i)^2 := by
  let b := hA.eigenvectorBasis
  have he (i : Fin N) : A.toEuclideanLin (b i) = hA.eigenvalues i • b i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hx : A.toEuclideanLin x = ∑ i, (b.repr x i*hA.eigenvalues i) • b i := by
    nth_rw 1 [← b.sum_repr x]
    rw [map_sum]
    simp_rw [map_smul,he,smul_smul]
  rw [hx,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right]
  have hi : ⟪x,b i⟫ = b.repr x i := by
    exact (real_inner_comm x (b i)).symm.trans (b.repr_apply_apply x i).symm
  calc
    _ = (b.repr x i*hA.eigenvalues i)*(b.repr x i) := congrArg _ hi
    _ = _ := by dsimp only [b]; ring

end InvariantIsing

end

end OAI
