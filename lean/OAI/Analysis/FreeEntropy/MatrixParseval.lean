import OAI.Analysis.FreeEntropy.MatrixBounds

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem coordinateMatrix_expand {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) :
    coordinateMatrix x i = ∑ j, ∑ k, (x (i,j,k) : ℂ) • hermitianBasis j k := by
  have hx : (WithLp.toLp 2 x : MatrixCoordinates n d) = ∑ q, x q • EuclideanSpace.single q 1 := by
    ext q
    simp [EuclideanSpace.single, Pi.single_apply]
  have he := congrArg (fun a : MatrixCoordinates n d => (hermitianChart n d a) i) hx
  change coordinateMatrix x i = _ at he
  rw [he]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  change (∑ q : MatrixIndex n d, x q • hermitianMatrix (EuclideanSpace.single q 1) i) = _
  simp only [Fintype.sum_prod_type, hermitianMatrix_single]
  simp only [smul_ite, smul_zero, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  ext a b
  exact Complex.real_smul
 theorem basis_pair_parseval {d : ℕ} (j k : Fin d) (D : Matrix (Fin d) (Fin d) ℂ) :
    Complex.normSq (Matrix.trace (hermitianBasis j k*D)) + Complex.normSq (Matrix.trace (hermitianBasis k j*D)) =
      Complex.normSq (D j k)+Complex.normSq (D k j) := by
  by_cases hjk : j=k
  · subst k; simp [hermitianBasis, Matrix.trace_single_mul]
  have hcalc (z w : ℂ) :
      Complex.normSq (((Real.sqrt 2 : ℂ)⁻¹)*(z+w)) +
      Complex.normSq (Complex.I*((Real.sqrt 2 : ℂ)⁻¹)*(w-z)) = Complex.normSq z+Complex.normSq w := by
    have hs : Complex.normSq ((Real.sqrt 2 : ℂ)⁻¹) = (1/2 : ℝ) := by
      simp [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    simp only [map_mul, hs, one_mul, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    ring
  rcases lt_or_gt_of_ne hjk with h | h
  · simpa [hermitianBasis, hjk, Ne.symm hjk, h, not_lt_of_gt h,
      smul_mul_assoc, Matrix.trace_smul, Matrix.add_mul, Matrix.sub_mul,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_single_mul, smul_eq_mul,
      add_comm, mul_add] using hcalc (D j k) (D k j)
  · simpa [hermitianBasis, hjk, Ne.symm hjk, h, not_lt_of_gt h,
      smul_mul_assoc, Matrix.trace_smul, Matrix.add_mul, Matrix.sub_mul,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_single_mul, smul_eq_mul,
      add_comm, mul_add] using hcalc (D k j) (D j k)
 theorem hermitianBasis_parseval {d : ℕ} (D : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, Complex.normSq (Matrix.trace (hermitianBasis j k*D))) = ∑ j, ∑ k, Complex.normSq (D j k) := by
  have hp := congrArg (fun f : Fin d → Fin d → ℝ => ∑ j, ∑ k, f j k)
    (funext (fun j => funext (fun k => basis_pair_parseval j k D)))
  simp only [sum_add_distrib] at hp
  have hswap : (∑ j : Fin d, ∑ k : Fin d, Complex.normSq (Matrix.trace (hermitianBasis k j*D))) =
      ∑ j : Fin d, ∑ k : Fin d, Complex.normSq (Matrix.trace (hermitianBasis j k*D)) := sum_comm
  have hswap' : (∑ j : Fin d, ∑ k : Fin d, Complex.normSq (D k j)) = ∑ j : Fin d, ∑ k : Fin d, Complex.normSq (D j k) := sum_comm
  rw [hswap,hswap'] at hp
  linarith
 theorem hermitianBasis_trace_bound {d : ℕ} (D : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, ‖Matrix.trace (hermitianBasis j k*D)‖^2) ≤ (d:ℝ)*matrixOpNorm D^2 := by
  simp_rw [← Complex.normSq_eq_norm_sq, hermitianBasis_parseval]
  exact matrix_frobenius_bound D
end FiniteEntropySeparation

end

end OAI
