import OAI.InformationTheory.Entanglement.Coherence

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n : Type} [Fintype n] [DecidableEq n]

def fidelity (A B : Mat n) : ℝ := traceNorm (CFC.sqrt A*CFC.sqrt B)
lemma sqrt_psd (A : Mat n) : (CFC.sqrt A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
lemma sqrt_herm (A : Mat n) : (CFC.sqrt A)ᴴ=CFC.sqrt A := (sqrt_psd A).isHermitian.eq

lemma traceNorm_conjTranspose (A : Mat n) : traceNorm Aᴴ=traceNorm A := by
  obtain ⟨U,hU,he⟩ := MatrixPolar.polar A
  conv_lhs => rw [he,Matrix.conjTranspose_mul,sqrt_herm,traceNorm_unitary_right _ (unitary_star hU)]
  conv_rhs => rw [he,traceNorm_unitary_left _ hU]

lemma sqrt_transpose {A : Mat n} (hA : A.PosSemidef) : CFC.sqrt Aᵀ=(CFC.sqrt A)ᵀ := by
  apply CFC.sqrt_unique
  · rw [← Matrix.transpose_mul,CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact (sqrt_psd A).transpose.nonneg

omit [Fintype n] [DecidableEq n] in
lemma conjugate_transpose_transpose (A : Mat n) : (Aᵀ)ᴴ=(Aᴴ)ᵀ := by
  ext i j
  rfl

lemma traceNorm_transpose (A : Mat n) : traceNorm Aᵀ=traceNorm A := by
  rw [← traceNorm_conjTranspose A]
  have hAA : (A*Aᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self Aᴴ
  unfold traceNorm
  rw [conjugate_transpose_transpose,← Matrix.transpose_mul,
    sqrt_transpose hAA,Matrix.trace_transpose,
    Matrix.conjTranspose_conjTranspose]

lemma fidelity_polar (A B : Mat n) : fidelity (Aᴴ*A) (Bᴴ*B)=traceNorm (A*Bᴴ) := by
  obtain ⟨U,hU,heA⟩ := MatrixPolar.polar A
  obtain ⟨V,hV,heB⟩ := MatrixPolar.polar B
  conv_rhs => rw [heA,heB,Matrix.conjTranspose_mul,sqrt_herm]
  rw [← Matrix.mul_assoc,Matrix.mul_assoc U,traceNorm_unitary_right _ (unitary_star hV),
    traceNorm_unitary_left _ hU]
  rfl

lemma fidelity_transpose {A B : Mat n} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fidelity Aᵀ Bᵀ=fidelity A B := by
  unfold fidelity
  rw [sqrt_transpose hA,sqrt_transpose hB,← Matrix.transpose_mul,traceNorm_transpose,
    ← traceNorm_conjTranspose (CFC.sqrt B*CFC.sqrt A),Matrix.conjTranspose_mul,
    sqrt_herm,sqrt_herm]

lemma unitary_trace_conj {U : Mat n} (hU : Uᴴ*U=1) (A : Mat n) :
    Matrix.trace (Uᴴ*A*U)=Matrix.trace A := by
  rw [Matrix.trace_mul_cycle,unitary_reverse hU,Matrix.one_mul]

lemma unitary_traceNorm_conj {U : Mat n} (hU : Uᴴ*U=1) (A : Mat n) :
    traceNorm (Uᴴ*A*U)=traceNorm A := by
  rw [traceNorm_unitary_right _ hU,traceNorm_unitary_left _ (unitary_star hU)]

lemma unitary_conj_mul {U : Mat n} (hU : Uᴴ*U=1) (A B : Mat n) :
    (Uᴴ*A*U)*(Uᴴ*B*U)=Uᴴ*(A*B)*U := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᴴ,unitary_reverse hU,Matrix.one_mul]
end SecretKey

end

end OAI
