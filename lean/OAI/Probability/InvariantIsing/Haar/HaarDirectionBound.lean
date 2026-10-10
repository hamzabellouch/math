import OAI.Probability.InvariantIsing.Haar.HaarPolynomialCurvature

namespace OAI

/-! Directional control by coordinate-plane derivatives. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma plane_functional_abs_bound {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A)
    (δ : ℝ) (hδ : ∀ i j, |ell (planeGenerator i j)| ≤ δ) :
    2*|ell A| ≤ (∑ i, ∑ j, |A i j|)*δ := by
  have hr := plane_functional_representation ell A hA
  rw [matrixFrobeniusPair_eq_sum] at hr
  change (∑ i, ∑ j, ell (planeGenerator i j)*A i j) = 2*ell A at hr
  have hs : |∑ i, ∑ j, ell (planeGenerator i j)*A i j| ≤
      (∑ i, ∑ j, |A i j|)*δ := by
    calc
      |∑ i, ∑ j, ell (planeGenerator i j)*A i j| ≤
          ∑ i, |∑ j, ell (planeGenerator i j)*A i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |ell (planeGenerator i j)*A i j| := by
        apply Finset.sum_le_sum; intro i _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |A i j| * δ := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_left (hδ i j) (abs_nonneg _)
      _ = (∑ i, ∑ j, |A i j|)*δ := by simp only [Finset.sum_mul]
  rw [hr,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hs
  exact hs

lemma matrixPolynomial_direction_bound {N : ℕ}
    (p : MatrixPolynomial N) (M A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : matrixPolynomialEval M (haarPolynomialGamma p p) ≤ δ^2) :
    2*|matrixPolynomialEval M (matrixPolynomialDerivation A p)| ≤
      (∑ i, ∑ j, |A i j|)*δ := by
  apply plane_functional_abs_bound (matrixPolynomialDifferential p M) A hA δ
  intro i j
  change |matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p)| ≤ δ
  have hpos (i j : Fin N) :
      0 ≤ (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p))^2 :=
    sq_nonneg _
  have htotal : matrixPolynomialEval M (haarPolynomialGamma p p) =
      ∑ i : Fin N, ∑ j : Fin N,
        (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p))^2 := by
    simp only [haarPolynomialGamma,map_sum,map_mul,pow_two]
  have hs : (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p))^2 ≤ δ^2 := by
    apply le_trans _ hp
    rw [htotal]
    exact (Finset.single_le_sum (fun k _ => hpos i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hpos k l)) (Finset.mem_univ i))
  exact (sq_le_sq₀ (abs_nonneg _) hδ).mp (by simpa only [sq_abs] using hs)

end InvariantIsing

end

end OAI
