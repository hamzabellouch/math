import OAI.Probability.SignedSweeps.WordDensity
import OAI.Probability.SignedSweeps.WordEntropy

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

theorem positive_matrix_sorted_diagonalization {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
    (hA : A.PosSemidef) (htrace : A.trace.re ≤ 1) :
    ∃ (x : Fin q → ℝ) (U : Matrix.unitaryGroup (Fin q) ℂ),
      Antitone x ∧ (∀ i, 0 ≤ x i) ∧ (∑ i, x i ≤ 1) ∧
      A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1 := by
  let T := A.toEuclideanLin
  have hT : T.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr hA
  have hn : finrank ℂ (EuclideanSpace ℂ (Fin q)) = q := by simp
  let x := hT.isSymmetric.eigenvalues hn
  let b := hT.isSymmetric.eigenvectorBasis hn
  let U : Matrix.unitaryGroup (Fin q) ℂ :=
    ⟨(EuclideanSpace.basisFun (Fin q) ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun (Fin q) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hU (i j : Fin q) : U.1 i j = b j i := rfl
  have he (i : Fin q) : T (b i) = (x i : ℂ) • b i :=
    hT.isSymmetric.apply_eigenvectorBasis hn i
  have hxn (i : Fin q) : 0 ≤ x i :=
    positive_scalar_nonneg T hT (x i : ℂ) (b.toBasis.ne_zero i) (he i)
  have hAU : A * U.1 = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hi := congrArg (fun v : EuclideanSpace ℂ (Fin q) => v i) (he j)
    simpa only [T, Matrix.toLpLin_apply, WithLp.ofLp_toLp, PiLp.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.mul_apply, hU,
      Matrix.mul_diagonal, mul_comm] using hi
  have hspec : A = U.1 * Matrix.diagonal (fun i => (x i : ℂ)) * star U.1 := by
    rw [← hAU, mul_assoc, U.2.2, mul_one]
  have ht : A.trace = ∑ i, (x i : ℂ) := by
    rw [hspec, Matrix.trace_mul_cycle, U.2.1, one_mul, Matrix.trace_diagonal]
  refine ⟨x, U, hT.isSymmetric.eigenvalues_antitone hn, hxn, ?_, hspec⟩
  have hr := congrArg Complex.re ht
  change Complex.reCLM A.trace = Complex.reCLM (∑ i, (x i : ℂ)) at hr
  simp only [map_sum, Complex.reCLM_apply, Complex.ofReal_re] at hr
  rwa [← hr]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma matrix_unitary_euclidean_norm (U : Matrix.unitaryGroup I ℂ)
    (v : EuclideanSpace ℂ I) : ‖U.1.toEuclideanLin v‖ = ‖v‖ := by
  let L := U.1.toEuclideanLin
  have he : L.adjoint * L = 1 := by
    change U.1.toEuclideanLin.adjoint * U.1.toEuclideanLin = 1
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change (Matrix.toLpLin 2 2 U.1.conjTranspose).comp (Matrix.toLpLin 2 2 U.1) = 1
    rw [← Matrix.toLpLin_mul_same]
    change Matrix.toLpLin 2 2 (star U.1 * U.1) = 1
    rw [U.2.1, Matrix.toLpLin_one]
    rfl
  have hh := LinearMap.adjoint_inner_right L v (L v)
  change inner ℂ v ((L.adjoint * L) v) = inner ℂ (L v) (L v) at hh
  rw [he] at hh
  have hr := congrArg Complex.re hh
  simp only [Module.End.one_apply, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re] at hr
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr).symm

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma wordTensor_preserves_isotypic {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p) (A : Matrix C C ℂ) {v : WordSpace p C}
    (hv : v ∈ (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p C)).toSubmodule) :
    (wordMatrixEquiv p C).symm (wordTensorMatrix p A) v ∈
      (isotypicSubrepresentation (spechtRepresentation μ)
        (wordRepresentation p C)).toSubmodule := by
  let L := (wordMatrixEquiv p C).symm (wordTensorMatrix p A)
  have hL : Representation.IsIntertwiningMap (wordRepresentation p C)
      (wordRepresentation p C) L := (wordMatrix_intertwining L).mpr (by
        simp only [L, StarAlgEquiv.apply_symm_apply]
        exact wordTensor_mem_commutant A)
  exact isotypic_end_stable _ _
    (L.intertwiningMap_of_isIntertwiningMap _ _ hL.isIntertwining) hv

theorem word_density_norm_le {p q : ℕ} (μ : Partition p) (hμ : μ.1.colLen 0 ≤ q)
    (A : Matrix (Fin q) (Fin q) ℂ) (hA : A.PosSemidef) (htrace : A.trace.re ≤ 1)
    (v : WordSpace p (Fin q))
    (hv : v ∈ (isotypicSubrepresentation (spechtRepresentation μ)
      (wordRepresentation p (Fin q))).toSubmodule) :
    ‖(wordMatrixEquiv p (Fin q)).symm (wordTensorMatrix p A) v‖ ≤
      Real.exp (-partsEntropy p μ.1.rowLens) * ‖v‖ := by
  obtain ⟨x, U, hx, hx0, hxs, he⟩ := positive_matrix_sorted_diagonalization A hA htrace
  let W := wordMatrixEquiv p (Fin q)
  let L := W.symm (wordTensorMatrix p U.1)
  let L' := W.symm (wordTensorMatrix p (star U.1))
  have hunit (R : Matrix (Fin q) (Fin q) ℂ) (hR : R ∈ Matrix.unitaryGroup (Fin q) ℂ) :
      wordTensorMatrix p R ∈ Matrix.unitaryGroup (Fin p → Fin q) ℂ := by
    have hI : wordTensorMatrix p (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
      ext w z
      by_cases h : w = z
      · subst z; simp [wordTensorMatrix]
      · rw [Matrix.one_apply_ne h]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)
    rw [Matrix.mem_unitaryGroup_iff] at hR ⊢
    change wordTensorMatrix p R * (wordTensorMatrix p R).conjTranspose = 1
    rw [← wordTensorMatrix_star, ← wordTensorMatrix_mul]
    change wordTensorMatrix p (R * star R) = 1
    rw [hR, hI]
  have hn (z : WordSpace p (Fin q)) : ‖L z‖ = ‖z‖ := by
    have hh := matrix_unitary_euclidean_norm ⟨_, hunit U.1 U.2⟩ z
    rw [show L = _ from wordMatrixEquiv_symm (wordTensorMatrix p U.1)]
    convert hh using 2
    ext i
    rfl
  have hn' (z : WordSpace p (Fin q)) : ‖L' z‖ = ‖z‖ := by
    have hh := matrix_unitary_euclidean_norm ⟨_, hunit (star U.1) (star U).2⟩ z
    rw [show L' = _ from wordMatrixEquiv_symm (wordTensorMatrix p (star U.1))]
    convert hh using 2
    ext i
    rfl
  have hv' := wordTensor_preserves_isotypic μ (star U.1) hv
  have hb := word_diagonal_density_norm_le μ hμ x hx hx0 hxs (L' v) hv'
  rw [he, wordTensorMatrix_mul, wordTensorMatrix_mul, map_mul, map_mul]
  change ‖L (W.symm (wordTensorMatrix p (Matrix.diagonal (fun i => (x i : ℂ)))) (L' v))‖ ≤ _
  simpa only [hn, hn'] using hb

end SignedSweeps
end

end OAI
