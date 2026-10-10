import OAI.Combinatorics.MatchingPSD.DeterminantNormalization

namespace OAI

universe u_1

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
lemma trace_mono_matrix {A B : Matrix R R ℝ} (h : A ≤ B) : A.trace ≤ B.trace :=
  (Matrix.tracePositiveLinearMap R ℝ ℝ).monotone h

lemma frobenius_sq (A : Matrix R R ℝ) :
    ‖A‖^2 = ∑ i, ∑ j, (A i j)^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp
  · positivity

lemma frobenius_sq_trace (A : Matrix R R ℝ) : ‖A‖^2 = (Aᵀ * A).trace := by
  rw [frobenius_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, ← pow_two]
  exact Finset.sum_comm

lemma square_le_self {A : Matrix R R ℝ} (hA : 0 ≤ A) (hA₁ : A ≤ 1) : A^2 ≤ A := by
  have hc : Commute A (1-A) := (Commute.one_right A).sub_right (Commute.refl A)
  have hh := Commute.mul_nonneg hA (sub_nonneg.mpr hA₁) hc
  simpa only [mul_sub, mul_one, ← pow_two, sub_nonneg] using hh

lemma transpose_mul_self_le_one {A : Matrix R R ℝ} (hA : 0 ≤ A) (hA₁ : A ≤ 1) :
    Aᵀ * A ≤ 1 := by
  have hh : Aᵀ = A := hA.posSemidef.isHermitian.eq
  rw [hh, ← pow_two]
  exact (square_le_self hA hA₁).trans hA₁

lemma frobenius_mul_contraction {A : Matrix R R ℝ} (hA : Aᵀ * A ≤ 1)
    (B : Matrix R R ℝ) : ‖A*B‖ ≤ ‖B‖ := by
  have h := hA.conjTranspose_mul_mul_same B
  have ht := h.trace_nonneg
  have hid : Bᴴ * (1 - Aᵀ * A) * B = Bᵀ * B - (A*B)ᵀ * (A*B) := by
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, mul_sub, sub_mul, mul_one,
      Matrix.transpose_mul, mul_assoc]
  rw [hid, Matrix.trace_sub, ← frobenius_sq_trace, ← frobenius_sq_trace] at ht
  nlinarith [norm_nonneg (A*B), norm_nonneg B]

lemma one_sub_square_le {A : Matrix R R ℝ} (hA : 0 ≤ A) (hA₁ : A ≤ 1) :
    (1-A)^2 ≤ 1-A := square_le_self (sub_nonneg.mpr hA₁) (by simpa using hA)

lemma test_error {ρ F : Matrix R R ℝ} (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hF : 0 ≤ F) (hF₁ : F ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hs : 1-ε ≤ (ρ*F).trace) :
    ‖(F-1)*CFC.sqrt ρ‖ ≤ Real.sqrt ε := by
  let G := CFC.sqrt ρ
  have hG : G.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hGG : G*G = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have he : ((F-1)*G)ᵀ * ((F-1)*G) = G*(1-F)^2*G := by
    have hFt : Fᵀ = F := hF.posSemidef.isHermitian.eq
    have hGt : Gᵀ = G := hG.isHermitian.eq
    rw [Matrix.transpose_mul, Matrix.transpose_sub, hFt, Matrix.transpose_one, hGt]
    noncomm_ring
  have hb := trace_mul_le_of_le hρ (one_sub_square_le hF hF₁)
  have hnorm : ‖(F-1)*G‖^2 ≤ ε := by
    rw [frobenius_sq_trace, he, Matrix.trace_mul_cycle, hGG]
    have hc : (ρ*(1-F)).trace = 1-(ρ*F).trace := by
      rw [mul_sub, mul_one, Matrix.trace_sub, htρ]
    rw [hc] at hb
    linarith
  change ‖(F-1)*G‖ ≤ Real.sqrt ε
  nlinarith [Real.sq_sqrt hε, Real.sqrt_nonneg ε, norm_nonneg ((F-1)*G)]

lemma posSemidef_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix R R ℝ) := by
  classical
  have he (i : R) : hA.isHermitian.eigenvalues i ≤ A.trace := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hd : (A.trace • (1 : Matrix R R ℝ) -
      Matrix.diagonal hA.isHermitian.eigenvalues).PosSemidef := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (he i))
  let U : Matrix R R ℝ := hA.isHermitian.eigenvectorUnitary
  have hu : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hs : A = U * Matrix.diagonal hA.isHermitian.eigenvalues * Uᴴ := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, U] using hA.isHermitian.spectral_theorem
  have hc := hd.conjTranspose_mul_mul_same Uᴴ
  have hc' : (A.trace • (1 : Matrix R R ℝ) -
      U * Matrix.diagonal hA.isHermitian.eigenvalues * Uᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose, mul_sub, sub_mul,
      mul_smul_comm, smul_mul_assoc, mul_one, hu] using hc
  rwa [← hs] at hc'

end PerfectMatchingPSD

end OAI
