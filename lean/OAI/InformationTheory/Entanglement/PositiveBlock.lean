import OAI.InformationTheory.Entanglement.TraceNorm

namespace OAI

noncomputable section
open scoped MatrixOrder ComplexOrder BigOperators Kronecker
open Matrix
namespace SecretKey
variable {n m k : Type} [Fintype n] [Fintype m] [Fintype k]

def hsVector (A : Matrix n m ℂ) : EuclideanSpace ℂ (n × m) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)
def hsNorm (A : Matrix n m ℂ) : ℝ := ‖hsVector A‖

lemma trace_mul_conj_eq_inner (A B : Matrix n m ℂ) :
    Matrix.trace (A * Bᴴ) = inner ℂ (hsVector B) (hsVector A) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, hsVector,
    PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply]

lemma hsNorm_sq (A : Matrix n m ℂ) :
    hsNorm A ^ 2 = (Matrix.trace (A * Aᴴ)).re := by
  rw [trace_mul_conj_eq_inner]
  exact norm_sq_eq_re_inner (𝕜 := ℂ) _

lemma trace_mul_conj_norm_le (A B : Matrix n m ℂ) :
    ‖Matrix.trace (A * Bᴴ)‖ ≤ hsNorm A * hsNorm B := by
  rw [trace_mul_conj_eq_inner]
  simpa [hsNorm, mul_comm] using norm_inner_le_norm (hsVector B) (hsVector A)

lemma hsNorm_unitary [DecidableEq n] {U : Matrix n n ℂ} (hU : Uᴴ * U = 1)
    (A : Matrix n m ℂ) : hsNorm (U * A) = hsNorm A := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change hsNorm (U * A) ^ 2 = hsNorm A ^ 2
  rw [hsNorm_sq, hsNorm_sq, Matrix.conjTranspose_mul]
  congr 1
  calc
    Matrix.trace (U * A * (Aᴴ * Uᴴ)) = Matrix.trace (U * (A * Aᴴ) * Uᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Uᴴ * U * (A * Aᴴ)) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (A * Aᴴ) := by rw [hU, Matrix.one_mul]

lemma traceNorm_mul_conj_le [DecidableEq n] (A B : Matrix n m ℂ) :
    traceNorm (A * Bᴴ) ≤ hsNorm A * hsNorm B := by
  obtain ⟨U,hU,he⟩ := traceNorm_witness (A * Bᴴ)
  rw [he, ← Matrix.mul_assoc]
  exact (Complex.re_le_norm _).trans
    ((trace_mul_conj_norm_le (U * A) B).trans_eq (by rw [hsNorm_unitary hU]))

lemma traceNorm_mul_conj_le_sqrt [DecidableEq n] (A B : Matrix n m ℂ) :
    traceNorm (A * Bᴴ) ≤ Real.sqrt ((Matrix.trace (A * Aᴴ)).re * (Matrix.trace (B * Bᴴ)).re) := by
  rw [← hsNorm_sq, ← hsNorm_sq, ← mul_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg (show 0 ≤ hsNorm A * hsNorm B from mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact traceNorm_mul_conj_le A B

lemma positive_block [DecidableEq n] (H J Z : Matrix n n ℂ)
    (h : (Matrix.fromBlocks H Z Zᴴ J).PosSemidef) :
    traceNorm Z ≤ Real.sqrt ((Matrix.trace H).re * (Matrix.trace J).re) := by
  let Q := CFC.sqrt (Matrix.fromBlocks H Z Zᴴ J)
  have hQh : Qᴴ = Q :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.eq
  have hQ : Q * Qᴴ = Matrix.fromBlocks H Z Zᴴ J := by
    rw [hQh]
    exact CFC.sqrt_mul_sqrt_self _ h.nonneg
  let A : Matrix n (n ⊕ n) ℂ := fun i j => Q (Sum.inl i) j
  let B : Matrix n (n ⊕ n) ℂ := fun i j => Q (Sum.inr i) j
  have hA : A * Aᴴ = H := by
    ext i j
    exact congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hQ
  have hB : B * Bᴴ = J := by
    ext i j
    exact congrArg (fun M => M (Sum.inr i) (Sum.inr j)) hQ
  have hZ : A * Bᴴ = Z := by
    ext i j
    exact congrArg (fun M => M (Sum.inl i) (Sum.inr j)) hQ
  simpa only [hA,hB,hZ] using traceNorm_mul_conj_le_sqrt A B
end SecretKey

end

end OAI
