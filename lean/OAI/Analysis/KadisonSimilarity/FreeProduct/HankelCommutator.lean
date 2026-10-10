import OAI.Analysis.KadisonSimilarity.FreeProduct.HankelOperator
import OAI.Analysis.KadisonSimilarity.Representation.Amplification

namespace OAI

/-!
# A finite Hankel matrix detects the base commutator

The constant-coordinate compression gives the tensor-product norm lower bound
needed by the paper without introducing any infinite matrix norm assumption.
-/

noncomputable section
namespace KadisonSimilarity

open Finset ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unnormalized constant-coordinate inclusion. -/
def constantCopies (N : ℕ) : H →L[ℂ] HilbertCopies H N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℂ H))

omit [CompleteSpace H] in
@[simp] theorem constantCopies_apply (N : ℕ) (x : H) (i : Fin N) :
    constantCopies N x i = x := by simp [constantCopies]

@[simp] theorem constantCopies_adjoint_apply (N : ℕ) (x : HilbertCopies H N) :
    (constantCopies N).adjoint x = ∑ i : Fin N, x i := by
  apply ext_inner_left ℂ
  intro y
  simp only [adjoint_inner_right, PiLp.inner_apply, constantCopies_apply, inner_sum]

omit [CompleteSpace H] in
theorem norm_constantCopies_le (N : ℕ) :
    ‖constantCopies (H := H) N‖ ≤ Real.sqrt N := by
  apply opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  simp

/-- Compressing a scalar operator matrix to constant coordinates sums all
its coefficients. -/
theorem constantCopies_compression (N : ℕ) (M : Matrix (Fin N) (Fin N) ℝ)
    (T : H →L[ℂ] H) :
    (constantCopies N).adjoint.comp
      ((matrixOperator (fun i j => (M i j : ℂ) • T)).comp (constantCopies N)) =
      ((∑ i : Fin N, ∑ j : Fin N, M i j : ℝ) : ℂ) • T := by
  ext x
  simp only [comp_apply, constantCopies_adjoint_apply]
  simp [matrixOperator, constantCopies, ← Finset.sum_smul, -Complex.ofReal_sum]

theorem norm_constantCopies_compression_le (N : ℕ)
    (T : HilbertCopies H N →L[ℂ] HilbertCopies H N) :
    ‖(constantCopies N).adjoint.comp (T.comp (constantCopies N))‖ ≤ N * ‖T‖ := by
  let V : H →L[ℂ] HilbertCopies H N := constantCopies N
  change ‖V.adjoint.comp (T.comp V)‖ ≤ (N : ℝ) * ‖T‖
  have hinner : ‖T.comp V‖ ≤ ‖T‖ * ‖V‖ := opNorm_comp_le T V
  have houter : ‖V.adjoint.comp (T.comp V)‖ ≤ ‖V.adjoint‖ * ‖T.comp V‖ :=
    opNorm_comp_le V.adjoint (T.comp V)
  have hV : ‖V‖ ≤ Real.sqrt N := norm_constantCopies_le N
  have hVs : ‖V.adjoint‖ ≤ Real.sqrt N := by rwa [adjoint.norm_map]
  calc
    _ ≤ ‖V.adjoint‖ * (‖T‖ * ‖V‖) :=
      houter.trans (mul_le_mul_of_nonneg_left hinner (norm_nonneg _))
    _ ≤ Real.sqrt N * (‖T‖ * Real.sqrt N) := by gcongr
    _ = (Real.sqrt N) ^ 2 * ‖T‖ := by ring
    _ = N * ‖T‖ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

/-- A matrix with coefficients bounded below by `c ≥ 0` detects a factor
`N * c` of the norm of its common operator entry. -/
theorem norm_scalar_operator_matrix_lower {N : ℕ} (hN : 0 < N)
    (M : Matrix (Fin N) (Fin N) ℝ) (T : H →L[ℂ] H) {c : ℝ}
    (hc : 0 ≤ c) (hM : ∀ i j, c ≤ M i j) :
    N * c * ‖T‖ ≤ ‖matrixOperator (fun i j => (M i j : ℂ) • T)‖ := by
  let s : ℝ := ∑ i : Fin N, ∑ j : Fin N, M i j
  have hsum : (N : ℝ) * (N * c) ≤ s := by
    calc
      _ = ∑ _i : Fin N, ∑ _j : Fin N, c := by simp
      _ ≤ s := sum_le_sum fun i _ => sum_le_sum fun j _ => hM i j
  have hs : 0 ≤ s := (by positivity : 0 ≤ (N : ℝ) * (N * c)).trans hsum
  have hcomp := norm_constantCopies_compression_le N
    (matrixOperator (fun i j => (M i j : ℂ) • T))
  rw [constantCopies_compression, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs] at hcomp
  have hmul := mul_le_mul_of_nonneg_right hsum (norm_nonneg T)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

/-- The actual narrow-arc matrix detects a uniform fraction of the base norm. -/
theorem norm_arc_operator_matrix_lower {N : ℕ} (hN : 0 < N) (T : H →L[ℂ] H) :
    (1 / Real.pi ^ 2) * ‖T‖ ≤
      ‖matrixOperator (fun i j => (arcHankelMatrix N i j : ℂ) • T)‖ := by
  have h := norm_scalar_operator_matrix_lower hN (arcHankelMatrix N) T
    (by unfold arcWidth; positivity) (arcHankelMatrix_entry_lower hN)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  convert h using 1
  unfold arcWidth
  field_simp

omit [CompleteSpace H] in
/-- Scalar diagonal terms vanish from the commutator. -/
theorem commutator_scalar_id_add (B S : H →L[ℂ] H) (a b : ℂ) :
    commutator B (a • ContinuousLinearMap.id ℂ H + b • S) = b • commutator B S := by
  change commutator B (a • (1 : H →L[ℂ] H) + b • S) = _
  simp only [commutator, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, smul_sub]
  abel

/-- The Toeplitz part of the finite Fourier compression contributes no
commutator; the Hankel part detects the base operator. -/
theorem norm_commutator_fourier_matrix_lower {N : ℕ} (hN : 0 < N)
    (B S : H →L[ℂ] H) (toeplitz : Matrix (Fin N) (Fin N) ℝ) :
    (1 / Real.pi ^ 2) * ‖commutator B S‖ ≤
      ‖commutator (amplify B N)
        (matrixOperator (fun i j => (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ H +
          (arcHankelMatrix N i j : ℂ) • S))‖ := by
  let X : Matrix (Fin N) (Fin N) (H →L[ℂ] H) := fun i j =>
    (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ H + (arcHankelMatrix N i j : ℂ) • S
  have hX := commutator_amplify_matrixOperator B X
  change _ ≤ ‖commutator (amplify B N) (matrixOperator X)‖
  rw [hX]
  simpa only [X, commutator_scalar_id_add] using norm_arc_operator_matrix_lower hN (commutator B S)

end KadisonSimilarity

end

end OAI
