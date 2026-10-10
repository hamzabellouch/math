import OAI.Probability.SignedSweeps.HilbertBlockNorm
import OAI.Probability.SignedSweeps.WordMonomial

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma matrix_unitary_diagonal_trace_re {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → ℝ) (U : Matrix.unitaryGroup I ℂ) (A : Matrix I I ℂ)
    (hAU : A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1) :
    A.trace.re = ∑ i, x i := by
  have he : A.trace = ∑ i, (x i : ℂ) := by
    rw [hAU, Matrix.trace_mul_cycle, U.2.1, one_mul, Matrix.trace_diagonal]
  rw [he]
  change Complex.reCLM (∑ i, (x i : ℂ)) = _
  simp only [map_sum, Complex.reCLM_apply, Complex.ofReal_re]

theorem pair_density_norm_le {u v p q : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (A B : Matrix (Fin q) (Fin q) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re + B.trace.re ≤ 1) (z : WordSpace p (Fin q ⊕ Fin q)) :
    ‖(((wordMatrixEquiv p (Fin q ⊕ Fin q)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) *
      pairTypeProjection h α β (Fin q)) z‖ ≤ Real.exp (-signedEntropy α β) * ‖z‖ := by
  have hAt : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hBt : 0 ≤ B.trace.re := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  obtain ⟨x,U,hx,hx0,_,hAU⟩ := positive_matrix_sorted_diagonalization A hA (by linarith)
  obtain ⟨y,V,hy,hy0,_,hBV⟩ := positive_matrix_sorted_diagonalization B hB (by linarith)
  have hxy : (∑ i, x i) + (∑ i, y i) ≤ 1 := by
    rwa [← matrix_unitary_diagonal_trace_re x U A hAU,
      ← matrix_unitary_diagonal_trace_re y V B hBV]
  have hb := pairTypeProjection_norm_of_factors h α β A B
    (Finset.prod_nonneg (fun i _ => hx0 _)) (Finset.prod_nonneg (fun i _ => hy0 _))
    (word_projection_monomial_norm_le α hα x hx hx0 U A hAU)
    (word_projection_monomial_norm_le β hβ y hy hy0 V B hBV) z
  exact hb.trans (mul_le_mul_of_nonneg_right
    (pair_rowColor_monomial_le α β hα hβ x y hx0 hy0 hxy) (norm_nonneg _))

lemma pair_density_opNorm_le {u v p q : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (A B : Matrix (Fin q) (Fin q) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re + B.trace.re ≤ 1) :
    ‖(((wordMatrixEquiv p (Fin q ⊕ Fin q)).symm (wordTensorMatrix p (Matrix.fromBlocks A 0 0 B))) *
      pairTypeProjection h α β (Fin q)).toContinuousLinearMap‖ ≤ Real.exp (-signedEntropy α β) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    (pair_density_norm_le h α β hα hβ A B hA hB htrace)

end SignedSweeps
end

end OAI
