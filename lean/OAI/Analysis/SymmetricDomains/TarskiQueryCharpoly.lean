import Mathlib
import OAI.Analysis.SymmetricDomains.HermiteSignature
import OAI.Analysis.SymmetricDomains.RootMomentCoefficients
import OAI.Analysis.SymmetricDomains.SignVariationsPositiveRoots

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination

section
open Matrix QuadraticMap Polynomial
open scoped BigOperators Classical
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma quadratic_matrix_apply (A : Matrix n n ℝ) (v : n → ℝ) :
    A.toQuadraticForm' v = v ⬝ᵥ (A *ᵥ v) := by
  exact Matrix.toLinearMap₂'_apply' _ _ _

lemma quadratic_matrix_comp (A B : Matrix n n ℝ) :
    A.toQuadraticForm'.comp B.mulVecLin = (Bᵀ * A * B).toQuadraticForm' := by
  apply QuadraticMap.ext
  intro v
  change A.toQuadraticForm' (B *ᵥ v) = (Bᵀ * A * B).toQuadraticForm' v
  simp only [quadratic_matrix_apply,← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

lemma diagonal_quadratic (w : n → ℝ) :
    (Matrix.diagonal w).toQuadraticForm' = weightedSumSquares ℝ w := by
  apply QuadraticMap.ext
  intro v
  simp only [quadratic_matrix_apply,dotProduct,
    weightedSumSquares_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  ring

lemma quadratic_signature_eigenvalues (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    signedSignature A.toQuadraticForm' = ∑ i, (SignType.sign (hA.eigenvalues i) : ℝ) := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hd : Uᵀ * A * U = Matrix.diagonal hA.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply,Function.comp_def,RCLike.ofReal_real_eq_id,
      id_eq,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hsur : Function.Surjective U.mulVecLin := by
    intro v
    refine ⟨(star U) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply,Matrix.mulVec_mulVec]
    change ((hA.eigenvectorUnitary : Matrix n n ℝ) * star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v = v
    rw [← Unitary.coe_star,Unitary.coe_mul_star_self,Matrix.one_mulVec]
  have hq := quadratic_matrix_comp A U
  rw [hd,diagonal_quadratic] at hq
  rw [← signature_weightedSumSquares,← hq]
  simp only [signedSignature,sigPos_comp_surjective _ _ hsur,sigNeg_comp_surjective _ _ hsur]

lemma signature_matrix_charpoly (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    signedSignature A.toQuadraticForm' =
      (A.charpoly.signVariations : ℝ) - ((A.charpoly.comp (-X)).signVariations : ℝ) := by
  rw [quadratic_signature_eigenvalues A hA,
    signVariations_eq_positive_roots hA.splits_charpoly,
    signVariations_eq_positive_roots hA.splits_charpoly.comp_neg_X]
  simp only [roots_comp_neg_X,hA.roots_charpoly_eq_eigenvalues,
    Multiset.countP_map,neg_pos,← Multiset.countP_eq_card_filter]
  rw [← signature_weightedSumSquares,signedSignature,
    QuadraticForm.sigPos_weightedSumSquares,QuadraticForm.sigNeg_weightedSumSquares]
  congr 1 <;> simp [Set.ncard_eq_toFinset_card',Multiset.countP_eq_card_filter] <;> rfl

end

open Polynomial Matrix QuadraticMap Finset
open scoped BigOperators Classical

noncomputable def hermiteMatrix (P Q : ℝ[X]) : Matrix (Fin P.natDegree) (Fin P.natDegree) ℝ :=
  fun i j => (((complexify P).roots.map
    (fun z => (complexify Q).eval z * z^(i.val+j.val))).sum).re

lemma hermiteMatrix_isHermitian (P Q : ℝ[X]) : (hermiteMatrix P Q).IsHermitian := by
  rw [Matrix.IsHermitian,conjTranspose_eq_transpose_of_trivial]
  ext i j
  simp only [transpose_apply,hermiteMatrix]
  rw [Nat.add_comm]

lemma root_matrix_identity {n : ℕ} (q z : ℂ) (v : Fin n → ℝ) :
    (q * (∑ i, (v i : ℂ)*z^i.val)^2).re =
      ∑ i, ∑ j, v i * (q*z^(i.val+j.val)).re * v j := by
  have he : q * (∑ i, (v i : ℂ)*z^i.val)^2 =
      ∑ i, ∑ j, (v i : ℂ) * (q*z^(i.val+j.val)) * (v j : ℂ) := by
    simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  rw [he]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,mul_zero]

lemma complexify_eval_degreeLT {n : ℕ} (A : degreeLT ℝ n) (z : ℂ) :
    (complexify A.val).eval z = ∑ i : Fin n, ((degreeLTEquiv ℝ n A i : ℝ) : ℂ)*z^i.val := by
  rw [complexify,eval_map,eval₂_eq_sum]
  exact (Polynomial.sum_fin (fun i (a : ℝ) => (a : ℂ)*z^i) (by simp)
    (mem_degreeLT.mp A.property)).symm

lemma hermiteMatrix_quadratic (P Q : ℝ[X]) :
    (hermiteMatrix P Q).toQuadraticForm' =
      (hermiteForm P Q).comp (degreeLTEquiv ℝ P.natDegree).symm.toLinearMap := by
  apply QuadraticMap.ext
  intro v
  rw [QuadraticMap.comp_apply,hermiteForm_apply]
  simp only [complexify_eval_degreeLT,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
    root_matrix_identity,Finset.sum_multiset_map_count,smul_sum]
  rw [quadratic_matrix_apply]
  simp only [dotProduct,Matrix.mulVec,hermiteMatrix,Finset.sum_multiset_map_count,
    Complex.re_sum,nsmul_eq_mul,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero,Finset.mul_sum,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro z _
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

lemma hermiteMatrix_signature {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X]) :
    signedSignature (hermiteMatrix P Q).toQuadraticForm' = tarskiQuery P Q := by
  rw [hermiteMatrix_quadratic,signedSignature,
    sigPos_comp_surjective _ _ (degreeLTEquiv ℝ P.natDegree).symm.surjective,
    sigNeg_comp_surjective _ _ (degreeLTEquiv ℝ P.natDegree).symm.surjective]
  exact hermite_signature hP Q

lemma hermiteMatrix_coefficients {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X])
    {d : ℕ} (hQ : Q.degree < d) (i j : Fin P.natDegree) :
    hermiteMatrix P Q i j = ∑ k : Fin d, Q.coeff k.val *
      MvPolynomial.eval (rootCoefficient P)
        (powerSumPolynomial P.natDegree (k.val+i.val+j.val)) := by
  have hq (z : ℂ) : (complexify Q).eval z =
      ∑ k : Fin d, (Q.coeff k.val : ℂ)*z^k.val := by
    rw [complexify,eval_map,eval₂_eq_sum]
    exact (Polynomial.sum_fin (fun i (a : ℝ) => (a : ℂ)*z^i) (by simp) hQ).symm
  have he : ((complexify P).roots.map
      (fun z => (complexify Q).eval z * z^(i.val+j.val))).sum =
      ∑ k : Fin d, (Q.coeff k.val : ℂ) *
        (((complexify P).roots.map (fun z => z^(k.val+i.val+j.val))).sum) := by
    simp only [hq,Finset.sum_mul,Finset.sum_multiset_map_count,
      smul_sum,nsmul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro z _
    simp only [pow_add]
    ring
  rw [hermiteMatrix,he]
  simp only [complexify,root_moment_coefficients hP,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem tarskiQuery_charpoly {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X]) :
    tarskiQuery P Q =
      ((hermiteMatrix P Q).charpoly.signVariations : ℝ) -
      (((hermiteMatrix P Q).charpoly.comp (-X)).signVariations : ℝ) := by
  rw [← hermiteMatrix_signature hP Q]
  exact signature_matrix_charpoly _ (hermiteMatrix_isHermitian P Q)

end Release061.SignElimination

end

end OAI
