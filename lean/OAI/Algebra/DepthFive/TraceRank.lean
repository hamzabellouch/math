import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace Problem335

/-- Cauchy--Schwarz with only the nonzero summands counted. -/
theorem sq_sum_le_support_card_mul_sum_sq {ι : Type*} [Fintype ι]
    (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card {i // f i ≠ 0} : ℝ) * ∑ i, f i ^ 2 := by
  classical
  let s := Finset.univ.filter (fun i => f i ≠ 0)
  have hsum : ∑ i ∈ s, f i = ∑ i, f i := by
    exact Finset.sum_filter_ne_zero _
  have hsq : ∑ i ∈ s, f i ^ 2 = ∑ i, f i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi his
    have hf : f i = 0 := by simpa [s] using his
    simp [hf]
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  simpa only [hsum, hsq, Fintype.card_subtype] using h

/-- The second spectral moment of a Hermitian matrix. -/
theorem hermitian_trace_sq_eq_sum_eigenvalues_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ) ^ 2) := by
  conv_lhs =>
    rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  simp [Matrix.diagonal_pow, Function.comp_def]

/-- The trace-rank bound used in the moment method. Positivity is not needed
for this squared formulation: Hermitian symmetry suffices. -/
theorem hermitian_trace_sq_le_rank_mul_trace_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.trace.re ^ 2 ≤ (A.rank : ℝ) * (A ^ 2).trace.re := by
  rw [hA.trace_eq_sum_eigenvalues, hermitian_trace_sq_eq_sum_eigenvalues_sq hA,
    hA.rank_eq_card_non_zero_eigs]
  simpa [← Complex.ofReal_pow] using
    sq_sum_le_support_card_mul_sum_sq hA.eigenvalues

/-- A nonzero Hermitian matrix has strictly positive second moment. -/
theorem hermitian_trace_sq_pos {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hne : A ≠ 0) :
    0 < (A ^ 2).trace.re := by
  have he : hA.eigenvalues ≠ 0 := by
    intro hz
    exact hne (hA.eigenvalues_eq_zero_iff.mp hz)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp he
  rw [hermitian_trace_sq_eq_sum_eigenvalues_sq hA]
  simp only [← Complex.ofReal_pow, Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

/-- The ratio form of the trace-rank bound. -/
theorem hermitian_rank_ge_trace_ratio {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hsecond : 0 < (A ^ 2).trace.re) :
    A.trace.re ^ 2 / (A ^ 2).trace.re ≤ (A.rank : ℝ) := by
  apply (div_le_iff₀ hsecond).2
  exact hermitian_trace_sq_le_rank_mul_trace_sq hA

/-- Applied to the Gram matrix, the moment method bounds the rank of the
original rectangular matrix. -/
theorem gram_rank_ge_trace_ratio {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℂ)
    (hsecond : 0 < ((A.conjTranspose * A) ^ 2).trace.re) :
    (A.conjTranspose * A).trace.re ^ 2 / ((A.conjTranspose * A) ^ 2).trace.re ≤ (A.rank : ℝ) := by
  have h := hermitian_rank_ge_trace_ratio (Matrix.isHermitian_conjTranspose_mul_self A) hsecond
  simpa only [Matrix.rank_conjTranspose_mul_self] using h

end Problem335

end

end OAI
