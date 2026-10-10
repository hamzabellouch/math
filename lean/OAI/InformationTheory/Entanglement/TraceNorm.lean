import OAI.InformationTheory.Entanglement.MatrixPolar
import OAI.InformationTheory.Entanglement.SecretDefinitions

namespace OAI

noncomputable section
open scoped MatrixOrder ComplexOrder BigOperators Kronecker
open Matrix
namespace SecretKey
variable {n : Type} [Fintype n] [DecidableEq n]

lemma unitary_reverse {U : Matrix n n ℂ} (h : Uᴴ * U = 1) : U * Uᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr h)
lemma unitary_mul {U V : Matrix n n ℂ} (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (U * V)ᴴ * (U * V) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ U V, hU, Matrix.one_mul, hV]
lemma unitary_star {U : Matrix n n ℂ} (h : Uᴴ * U = 1) : (Uᴴ)ᴴ * Uᴴ = 1 := by
  rw [Matrix.conjTranspose_conjTranspose, unitary_reverse h]

lemma unitary_entry_norm_le {U : Matrix n n ℂ} (h : Uᴴ * U = 1) (i j : n) :
    ‖U i j‖ ≤ 1 := by
  have hs : (∑ k, ‖U k j‖ ^ 2) = 1 := by
    have hh := congrArg Complex.re (congrFun (congrFun h j) j)
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.conj_mul', Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re,
      Matrix.one_apply_eq, Complex.one_re] using hh
  have hl := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => sq_nonneg ‖U k j‖)
    (Finset.mem_univ i)
  rw [hs] at hl
  nlinarith [norm_nonneg (U i j)]

lemma trace_mul_diagonal (A : Matrix n n ℂ) (d : n → ℂ) :
    Matrix.trace (A * Matrix.diagonal d) = ∑ i, A i i * d i := by
  simp [Matrix.trace]

lemma trace_mul_psd_norm_le {H U : Matrix n n ℂ} (hH : H.PosSemidef)
    (hU : Uᴴ * U = 1) : ‖Matrix.trace (U * H)‖ ≤ (Matrix.trace H).re := by
  let V : Matrix n n ℂ := hH.isHermitian.eigenvectorUnitary
  have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self _
  have hspec : H = V * Matrix.diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) * Vᴴ := by
    simpa only [V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hH.isHermitian.spectral_theorem
  let W : Matrix n n ℂ := Vᴴ * U * V
  have hW : Wᴴ * W = 1 := unitary_mul (unitary_mul (unitary_star hV) hU) hV
  have ht : Matrix.trace (U * H) =
      ∑ i, W i i * (hH.isHermitian.eigenvalues i : ℂ) := by
    conv_lhs => rw [hspec, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_diagonal]
  rw [ht, hH.isHermitian.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum]
  calc
    ‖∑ i, W i i * (hH.isHermitian.eigenvalues i : ℂ)‖ ≤
        ∑ i, ‖W i i * (hH.isHermitian.eigenvalues i : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, hH.isHermitian.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hH.eigenvalues_nonneg i)]
      exact mul_le_of_le_one_left (hH.eigenvalues_nonneg i) (unitary_entry_norm_le hW i i)

omit [DecidableEq n] in
lemma traceNorm_nonneg {m : Type} [Fintype m] (A : Matrix n m ℂ) : 0 ≤ traceNorm A := by
  classical
  exact (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg).1

lemma traceNorm_of_psd {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    traceNorm H = (Matrix.trace H).re := by
  unfold traceNorm
  rw [hH.isHermitian.eq, CFC.sqrt_mul_self H hH.nonneg]

lemma traceNorm_unitary_left (A : Matrix n n ℂ) {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    traceNorm (U * A) = traceNorm A := by
  unfold traceNorm
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U A, hU,
    Matrix.one_mul]

lemma traceNorm_unitary_right (A : Matrix n n ℂ) {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    traceNorm (A * U) = traceNorm A := by
  let H := CFC.sqrt (Aᴴ * A)
  have hH : H.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hHsq : H * H = Aᴴ * A :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have h : CFC.sqrt ((A * U)ᴴ * (A * U)) = Uᴴ * H * U := by
    apply CFC.sqrt_unique
    · rw [Matrix.conjTranspose_mul]
      calc
        Uᴴ * H * U * (Uᴴ * H * U) = Uᴴ * H * (U * Uᴴ) * H * U := by
          simp only [Matrix.mul_assoc]
        _ = Uᴴ * (H * H) * U := by rw [unitary_reverse hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = Uᴴ * Aᴴ * (A * U) := by rw [hHsq]; simp only [Matrix.mul_assoc]
    · simpa using (hH.mul_mul_conjTranspose_same Uᴴ).nonneg
  unfold traceNorm
  rw [h, Matrix.trace_mul_cycle, unitary_reverse hU, Matrix.one_mul]

lemma trace_unitary_norm_le (A : Matrix n n ℂ) {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    ‖Matrix.trace (U * A)‖ ≤ traceNorm A := by
  obtain ⟨V,hV,he⟩ := MatrixPolar.polar A
  conv_lhs => rw [he, ← Matrix.mul_assoc]
  exact trace_mul_psd_norm_le (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))
    (unitary_mul hU hV)

lemma traceNorm_witness (A : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ traceNorm A = (Matrix.trace (U * A)).re := by
  obtain ⟨V,hV,he⟩ := MatrixPolar.polar A
  refine ⟨Vᴴ,unitary_star hV,?_⟩
  conv_rhs => rw [he, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  rfl

lemma trace_re_le_traceNorm (A : Matrix n n ℂ) : (Matrix.trace A).re ≤ traceNorm A := by
  calc
    (Matrix.trace A).re ≤ ‖Matrix.trace A‖ := Complex.re_le_norm _
    _ ≤ traceNorm A := by simpa using trace_unitary_norm_le A (U := 1) (by simp)

lemma traceNorm_add_le (A B : Matrix n n ℂ) : traceNorm (A+B) ≤ traceNorm A + traceNorm B := by
  obtain ⟨U,hU,he⟩ := traceNorm_witness (A+B)
  rw [he, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  apply add_le_add
  · exact (Complex.re_le_norm _).trans (trace_unitary_norm_le A hU)
  · exact (Complex.re_le_norm _).trans (trace_unitary_norm_le B hU)

end SecretKey

end

end OAI
