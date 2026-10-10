import OAI.LinearAlgebra.CirculantHadamard.Basic

namespace OAI

universe uR

/-!
# From real sign matrices to integer cyclic autocorrelation

The Gram entry is reindexed using translation in `Fin n`. The real/integer
bridge uses the injective coefficient map `ℤ → ℝ`; it does not assume any
classification or any group-ring norm statement.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {n : ℕ}

/-- An integer sign row with the full Hadamard Gram equation. -/
def IsIntegerSignRow (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧
    rowCirculant h * (rowCirculant h).transpose =
      (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

/-- The Gram entry at `(i,a)` is the cyclic autocorrelation at `a-i`. -/
theorem rowCirculant_gram_apply [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) (i a : Fin n) :
    (rowCirculant h * (rowCirculant h).transpose) i a =
      ∑ j, h j * h (j - (a - i)) := by
  classical
  let e : Fin n ≃ Fin n :=
    { toFun := fun j => j - i
      invFun := fun j => j + i
      left_inv := fun j => sub_add_cancel j i
      right_inv := fun j => add_sub_cancel_right j i }
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant_apply]
  apply Fintype.sum_equiv e
  intro j
  change h (j - i) * h (j - a) = h (j - i) * h ((j - i) - (a - i))
  simp only [sub_sub_sub_cancel_right]

/-- The full Gram equation is exactly the cyclic autocorrelation system. -/
theorem gram_eq_iff_autocorrelation [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) :
    rowCirculant h * (rowCirculant h).transpose =
        (n : R) • (1 : Matrix (Fin n) (Fin n) R) ↔
      ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : R) else 0 := by
  classical
  constructor
  · intro hGram a
    have ha := congrArg (fun M : Matrix (Fin n) (Fin n) R => M 0 a) hGram
    rw [rowCirculant_gram_apply] at ha
    simpa [Matrix.smul_apply, Matrix.one_apply, eq_comm] using ha
  · intro hCorr
    ext i a
    rw [rowCirculant_gram_apply, hCorr]
    by_cases hia : i = a
    · subst a
      simp
    · have hai : a - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hia)
      simp [hia, hai, Matrix.smul_apply]

/-- Casting the integer Gram matrix agrees entry by entry with taking the
Gram matrix after casting the row. -/
theorem intCast_gram_apply (h : Fin n → ℤ) (i j : Fin n) :
    ((rowCirculant h * (rowCirculant h).transpose) i j : ℝ) =
      (rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose) i j := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant, Int.cast_sum,
    Int.cast_mul]

private theorem intCast_scaled_identity_apply (i j : Fin n) :
    (((n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) i j : ℝ) =
      ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) i j := by
  by_cases hij : i = j <;> simp [Matrix.smul_apply, hij]

/-- The real coefficient embedding preserves and reflects the entire Gram
identity, including the diagonal value. -/
theorem gram_intCast_iff (h : Fin n → ℤ) :
    rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose =
        (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ↔
      rowCirculant h * (rowCirculant h).transpose =
        (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  constructor
  · intro hGram
    ext i j
    apply Int.cast_injective (α := ℝ)
    rw [intCast_gram_apply, intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hGram
  · intro hGram
    ext i j
    rw [← intCast_gram_apply, ← intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => (M i j : ℝ)) hGram

/-- Every integer sign row gives the actual real circulant Hadamard matrix. -/
theorem IsIntegerSignRow.exists_real {h : Fin n → ℤ} (hh : IsIntegerSignRow h) :
    ExistsRealCirculantHadamard n := by
  refine ⟨rowCirculant (fun a => (h a : ℝ)), rowCirculant_isCirculant _, ?_,
    (gram_intCast_iff h).mpr hh.2⟩
  intro i j
  rcases hh.1 (j - i) with hpos | hneg
  · left
    simp only [rowCirculant_apply, hpos, Int.cast_one]
  · right
    simp only [rowCirculant_apply, hneg, Int.cast_neg, Int.cast_one]

/-- A real sign matrix determines an integer sign row without approximation. -/
theorem ExistsRealCirculantHadamard.exists_integerSignRow [NeZero n]
    (hH : ExistsRealCirculantHadamard n) : ∃ h : Fin n → ℤ, IsIntegerSignRow h := by
  classical
  rcases hH with ⟨H, ⟨h, hrow⟩, hsign, hGram⟩
  have hsignRow : ∀ j, IsSign (h j) := by
    intro j
    simpa only [hrow, sub_zero] using hsign 0 j
  let z : Fin n → ℤ := fun j => if h j = 1 then 1 else -1
  have hzcast : ∀ j, (z j : ℝ) = h j := by
    intro j
    by_cases hj : h j = 1
    · simp [z, hj]
    · have hneg := (hsignRow j).resolve_left hj
      simp only [z, ite_eq_right hj, Int.cast_neg, Int.cast_one, hneg]
  have hzsign : ∀ j, IsSign (z j) := by
    intro j
    dsimp [z, IsSign]
    split_ifs <;> simp
  have hzH : rowCirculant (fun j => (z j : ℝ)) = H := by
    ext i j
    rw [rowCirculant_apply, hzcast, hrow]
  refine ⟨z, hzsign, (gram_intCast_iff z).mp ?_⟩
  simpa only [hzH] using hGram

/-- Equivalence between the public real matrix problem and integer sign rows. -/
theorem integerSignRow_iff_real [NeZero n] :
    (∃ h : Fin n → ℤ, IsIntegerSignRow h) ↔ ExistsRealCirculantHadamard n := by
  constructor
  · rintro ⟨h, hh⟩
    exact hh.exists_real
  · exact ExistsRealCirculantHadamard.exists_integerSignRow

/-- A direct integer autocorrelation presentation of the real matrix problem. -/
theorem existsReal_iff_integer_autocorrelation [NeZero n] :
    ExistsRealCirculantHadamard n ↔
      ∃ h : Fin n → ℤ, (∀ j, IsSign (h j)) ∧
        ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : ℤ) else 0 := by
  rw [← integerSignRow_iff_real]
  simp only [IsIntegerSignRow, gram_eq_iff_autocorrelation]

end CirculantHadamard

end OAI
