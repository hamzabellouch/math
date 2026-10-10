import OAI.Geometry.EinsteinFour.DirichletMatrix

namespace OAI

/-! The tridiagonal Jacobi matrix and its ordered Schur pivots. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- The Dirichlet matrix with diagonal blocks `D` and both off-diagonals `-1`. -/
def dirichletMatrix {N : ℕ} (D : Fin N → NormalMatrix) :
    Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ := fun i j =>
  if i.2 = j.2 then D i.2 i.1 j.1
  else if i.2.val + 1 = j.2.val ∨ j.2.val + 1 = i.2.val then
    -(1 : NormalMatrix) i.1 j.1 else 0

/-- The diagonal determined by the pivots. The predecessor sum has at most
one term; its use also covers the first node without a separate convention. -/
def pivotDiagonal {N : ℕ} (S : Fin N → NormalMatrix) (i : Fin N) : NormalMatrix :=
  S i + ∑ k, if k.val + 1 = i.val then (S k)⁻¹ else 0

private theorem blockAt_lower {N : ℕ} (A : Fin N → NormalMatrix) (i k : Fin N) :
    blockAt (lowerBidiagonal A) i k =
      if i = k then 1 else if k.val + 1 = i.val then A k else 0 := by
  ext a b
  by_cases h : i = k
  · simp [blockAt, lowerBidiagonal, h]
  · by_cases hs : k.val + 1 = i.val <;> simp [blockAt, lowerBidiagonal, h, hs]

private theorem blockAt_dirichlet {N : ℕ} (D : Fin N → NormalMatrix) (i j : Fin N) :
    blockAt (dirichletMatrix D) i j =
      if i = j then D i else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  ext a b
  by_cases h : i = j
  · simp [blockAt, dirichletMatrix, h]
  · by_cases hs : i.val + 1 = j.val ∨ j.val + 1 = i.val <;>
      simp [blockAt, dirichletMatrix, h, hs]

private theorem pivot_left_block {N : ℕ} (S : Fin N → NormalMatrix)
    (hS : ∀ k, IsUnit (S k).det) (i k : Fin N) :
    blockAt (lowerBidiagonal (fun k => -(S k)⁻¹) * Matrix.blockDiagonal S) i k =
      if i = k then S k else if k.val + 1 = i.val then -1 else 0 := by
  rw [blockAt_mul_diagonal, blockAt_lower]
  by_cases h : i = k
  · simp [h]
  · by_cases hs : k.val + 1 = i.val
    · simp [h, hs, Matrix.nonsing_inv_mul _ (hS k)]
    · simp [h, hs]

private theorem pivot_right_block {N : ℕ} (S : Fin N → NormalMatrix)
    (hS : ∀ k, (S k).transpose = S k) (j k : Fin N) :
    blockAt (lowerBidiagonal (fun k => -(S k)⁻¹)).transpose k j =
      if j = k then 1 else if k.val + 1 = j.val then -(S k)⁻¹ else 0 := by
  rw [blockAt_transpose, blockAt_lower]
  by_cases h : j = k
  · simp [h]
  · by_cases hs : k.val + 1 = j.val
    · simp [h, hs, Matrix.transpose_nonsing_inv, hS]
    · simp [h, hs]

private theorem pivot_summand {N : ℕ} (S : Fin N → NormalMatrix)
    (hS : ∀ k, IsUnit (S k).det) (i j k : Fin N) :
    (if i = k then S k else if k.val + 1 = i.val then -1 else 0) *
      (if j = k then 1 else if k.val + 1 = j.val then -(S k)⁻¹ else 0) =
    (if i = k ∧ j = k then S k else 0) +
      (if i = k ∧ k.val + 1 = j.val then -1 else 0) +
      (if j = k ∧ k.val + 1 = i.val then -1 else 0) +
      (if k.val + 1 = i.val ∧ k.val + 1 = j.val then (S k)⁻¹ else 0) := by
  by_cases hik : i = k <;> by_cases hjk : j = k <;>
    by_cases hki : k.val + 1 = i.val <;> by_cases hkj : k.val + 1 = j.val
  all_goals simp_all [Matrix.mul_nonsing_inv _ (hS k)]

/-- The precise block formula before the predecessor sums are collapsed. -/
theorem pivot_factorization_blocks {N : ℕ} (S : Fin N → NormalMatrix)
    (hunit : ∀ k, IsUnit (S k).det) (hsym : ∀ k, (S k).transpose = S k)
    (i j : Fin N) :
    blockAt (lowerBidiagonal (fun k => -(S k)⁻¹) * Matrix.blockDiagonal S *
      (lowerBidiagonal (fun k => -(S k)⁻¹)).transpose) i j =
    (∑ k, if i = k ∧ j = k then S k else 0) +
      (∑ k, if i = k ∧ k.val + 1 = j.val then -1 else 0) +
      (∑ k, if j = k ∧ k.val + 1 = i.val then -1 else 0) +
      (∑ k, if k.val + 1 = i.val ∧ k.val + 1 = j.val then (S k)⁻¹ else 0) := by
  rw [blockAt_mul]
  simp_rw [pivot_left_block S hunit, pivot_right_block S hsym, pivot_summand S hunit,
    Finset.sum_add_distrib]

private theorem pivot_sum_collapse {N : ℕ} (S : Fin N → NormalMatrix) (i j : Fin N) :
    (∑ k, if i = k ∧ j = k then S k else 0) +
      (∑ k, if i = k ∧ k.val + 1 = j.val then -1 else 0) +
      (∑ k, if j = k ∧ k.val + 1 = i.val then -1 else 0) +
      (∑ k, if k.val + 1 = i.val ∧ k.val + 1 = j.val then (S k)⁻¹ else 0) =
    if i = j then pivotDiagonal S i
      else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hbad (k : Fin N) : ¬(i = k ∧ k.val + 1 = i.val) := by omega
    simp [hbad, pivotDiagonal]
  · have hfirst (k : Fin N) : ¬(i = k ∧ j = k) := by
      rintro ⟨hi, hj⟩
      exact hij (hi.trans hj.symm)
    have hlast (k : Fin N) : ¬(k.val + 1 = i.val ∧ k.val + 1 = j.val) := by omega
    simp only [hfirst, hlast, ite_false, Finset.sum_const_zero, zero_add, add_zero]
    have hsecond : (∑ k : Fin N, if i = k ∧ k.val + 1 = j.val then (-1 : NormalMatrix) else 0) =
        if i.val + 1 = j.val then -1 else 0 := by simp [ite_and]
    have hthird : (∑ k : Fin N, if j = k ∧ k.val + 1 = i.val then (-1 : NormalMatrix) else 0) =
        if j.val + 1 = i.val then -1 else 0 := by simp [ite_and]
    rw [hsecond, hthird, ite_eq_right hij]
    by_cases hf : i.val + 1 = j.val
    · have hb : ¬j.val + 1 = i.val := by omega
      simp [hf, hb]
    · by_cases hb : j.val + 1 = i.val <;> simp [hf, hb]

/-- The full tridiagonal matrix is the `L D Lᵀ` factorization of its Schur
pivots, with neither time ordering nor matrix multiplication commuted. -/
theorem dirichlet_pivot_factorization {N : ℕ} (S : Fin N → NormalMatrix)
    (hunit : ∀ k, IsUnit (S k).det) (hsym : ∀ k, (S k).transpose = S k) :
    dirichletMatrix (pivotDiagonal S) =
      lowerBidiagonal (fun k => -(S k)⁻¹) * Matrix.blockDiagonal S *
        (lowerBidiagonal (fun k => -(S k)⁻¹)).transpose := by
  have hb (i j : Fin N) :
      blockAt (dirichletMatrix (pivotDiagonal S)) i j =
      blockAt (lowerBidiagonal (fun k => -(S k)⁻¹) * Matrix.blockDiagonal S *
        (lowerBidiagonal (fun k => -(S k)⁻¹)).transpose) i j := by
    rw [blockAt_dirichlet, pivot_factorization_blocks S hunit hsym, pivot_sum_collapse]
  ext ⟨a, i⟩ ⟨b, j⟩
  exact congrFun (congrFun (hb i j) a) b

theorem det_dirichlet_pivots {N : ℕ} (S : Fin N → NormalMatrix)
    (hunit : ∀ k, IsUnit (S k).det) (hsym : ∀ k, (S k).transpose = S k) :
    (dirichletMatrix (pivotDiagonal S)).det = ∏ i, (S i).det := by
  rw [dirichlet_pivot_factorization S hunit hsym, det_bidiagonal_factorization]

theorem dirichlet_pivots_posDef {N : ℕ} (S : Fin N → NormalMatrix)
    (hS : ∀ i, (S i).PosDef) : (dirichletMatrix (pivotDiagonal S)).PosDef := by
  have hunit (i : Fin N) : IsUnit (S i).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hS i).isUnit
  have hsym (i : Fin N) : (S i).transpose = S i := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (hS i).isHermitian.eq
  rw [dirichlet_pivot_factorization S hunit hsym]
  exact bidiagonal_factorization_posDef _ _ hS

end

end PositiveEinsteinFour.Jacobi

end OAI
