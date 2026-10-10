import Mathlib

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open scoped BigOperators ComplexOrder

variable {d : ℕ}

def realTrace (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := A.trace.re

def traceSign (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  if 0 ≤ realTrace A then 1 else -1

theorem traceSign_mem (A : Matrix (Fin d) (Fin d) ℂ) :
    traceSign A = -1 ∨ traceSign A = 1 := by
  unfold traceSign
  split_ifs <;> simp

theorem nonzero_eigenvalues_card_le (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ A.rank := by
  classical
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  have hr : (Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)).rank
      ≤ A.rank := by
    rw [← h]
    simp only [Unitary.conjStarAlgAut_apply]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [Matrix.rank_diagonal] at hr
  simpa only [Function.comp_apply, ne_eq, RCLike.ofReal_eq_zero] using hr

theorem nonzero_eigenvalue_unique (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1)
    (i j : Fin d) (hi : hA.eigenvalues i ≠ 0) (hj : hA.eigenvalues j ≠ 0) :
    i = j := by
  have hcard : Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ 1 :=
    (nonzero_eigenvalues_card_le A hA).trans hrank
  have hs := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact congrArg Subtype.val (hs.elim (⟨i, hi⟩ : {i // hA.eigenvalues i ≠ 0}) ⟨j, hj⟩)

theorem eigenvalue_eq_realTrace (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1)
    (i : Fin d) (hi : hA.eigenvalues i ≠ 0) :
    hA.eigenvalues i = realTrace A := by
  classical
  unfold realTrace
  rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
  symm
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hj : hA.eigenvalues j = 0 := by
      by_contra hj
      exact hji (nonzero_eigenvalue_unique A hA hrank j i hj hi)
    simp [hj]
  · simp

theorem eigenvalue_eq_zero_or_trace (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) (i : Fin d) :
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = realTrace A := by
  by_cases hi : hA.eigenvalues i = 0
  · exact Or.inl hi
  · exact Or.inr (eigenvalue_eq_realTrace A hA hrank i hi)

theorem realTrace_eq_zero_iff (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) :
    realTrace A = 0 ↔ A = 0 := by
  constructor
  · intro ht
    apply hA.eigenvalues_eq_zero_iff.mp
    funext i
    rcases eigenvalue_eq_zero_or_trace A hA hrank i with hi | hi
    · exact hi
    · exact hi.trans ht
  · rintro rfl
    simp [realTrace]

theorem traceSign_mul_trace (A : Matrix (Fin d) (Fin d) ℂ) :
    traceSign A * realTrace A = |realTrace A| := by
  unfold traceSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem traceSign_sq (A : Matrix (Fin d) (Fin d) ℂ) :
    traceSign A * traceSign A = 1 := by
  rcases traceSign_mem A with h | h <;> rw [h] <;> norm_num

theorem traceSign_smul_posSemidef (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) :
    (traceSign A • A).PosSemidef := by
  change ((traceSign A : ℂ) • A).PosSemidef
  have hd : ((traceSign A : ℂ) • Matrix.diagonal
      ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)).PosSemidef := by
    rw [← Matrix.diagonal_smul]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    change 0 ≤ (traceSign A : ℂ) * (hA.eigenvalues i : ℂ)
    rw [← Complex.ofReal_mul, Complex.zero_le_real]
    rcases eigenvalue_eq_zero_or_trace A hA hrank i with hi | hi
    · simp [hi]
    · rw [hi, traceSign_mul_trace]
      exact abs_nonneg _
  have hp := hd.mul_mul_conjTranspose_same (↑hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have he := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at he
  simpa only [Matrix.smul_mul, Matrix.mul_smul, ← he] using hp

theorem rank_one_square (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) :
    A * A = realTrace A • A := by
  let D : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal
    ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)
  have hd : D * D = (realTrace A : ℂ) • D := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    congr 1
    funext i
    change (hA.eigenvalues i : ℂ) * (hA.eigenvalues i : ℂ) =
      (realTrace A : ℂ) * (hA.eigenvalues i : ℂ)
    rcases eigenvalue_eq_zero_or_trace A hA hrank i with hi | hi
    · simp [hi]
    · rw [hi]
  have he : A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary D := hA.spectral_theorem
  calc
    A * A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary (D * D) := by
      rw [map_mul, ← he]
    _ = (realTrace A : ℂ) • A := by rw [hd, map_smul, ← he]
    _ = realTrace A • A := by ext i j; simp [Complex.real_smul]

theorem realTrace_smul (r : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    realTrace (r • A) = r * realTrace A := by
  simp [realTrace, Matrix.trace, Matrix.diag, Finset.mul_sum]

end
end CurrentKS

end OAI
