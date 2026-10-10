import Mathlib

namespace OAI


namespace Problem355.PivotAssembly

open Matrix

variable {R : Type*} [CommRing R]

theorem exists_unit_pivot_reduction
    (C : Matrix (Fin 3) (Fin 3) R) (h : IsUnit (C 0 0)) :
    ∃ P Q : Matrix (Fin 3) (Fin 3) R,
      IsUnit P.det ∧ IsUnit Q.det ∧
      ∃ a b c d : R, P * C * Q = !![1, 0, 0; 0, a, b; 0, c, d] := by
  obtain ⟨u, hu⟩ := h
  let v : R := ↑u⁻¹
  have huv : C 0 0 * v = 1 := by simp [v, ← hu]
  have hvu : v * C 0 0 = 1 := by simp [v, ← hu]
  have hvux (x : R) : v * (C 0 0 * x) = x := by rw [← mul_assoc, hvu, one_mul]
  let P : Matrix (Fin 3) (Fin 3) R :=
    !![v, 0, 0; -(C 1 0 * v), 1, 0; -(C 2 0 * v), 0, 1]
  let Q : Matrix (Fin 3) (Fin 3) R :=
    !![1, -(v * C 0 1), -(v * C 0 2); 0, 1, 0; 0, 0, 1]
  refine ⟨P, Q, ?_, ?_,
    C 1 1 - C 1 0 * v * C 0 1,
    C 1 2 - C 1 0 * v * C 0 2,
    C 2 1 - C 2 0 * v * C 0 1,
    C 2 2 - C 2 0 * v * C 0 2, ?_⟩
  · simp [P, v, Matrix.det_fin_three]
  · simp [Q, Matrix.det_fin_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Q, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, add_mul,
        mul_assoc, hvu] <;> ring_nf <;>
      simp [pow_two, mul_assoc, hvux] <;> ring

def embedTwo (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

theorem embedTwo_mul (A B : Matrix (Fin 2) (Fin 2) R) :
    embedTwo (A * B) = embedTwo A * embedTwo B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedTwo, Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_embedTwo (A : Matrix (Fin 2) (Fin 2) R) :
    (embedTwo A).det = A.det := by
  simp [embedTwo, Matrix.det_fin_three, Matrix.det_fin_two]

theorem embedTwo_diagonal (a b : R) :
    embedTwo (Matrix.diagonal ![a, b]) = Matrix.diagonal ![1, a, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedTwo, Matrix.diagonal]

theorem exists_diagonal_of_two_by_two (rel : R → R → Prop)
    (hdiag : ∀ A : Matrix (Fin 2) (Fin 2) R,
      ∃ P Q : Matrix (Fin 2) (Fin 2) R,
        IsUnit P.det ∧ IsUnit Q.det ∧ ∃ a b : R,
          rel a b ∧ P * A * Q = Matrix.diagonal ![a, b])
    (C : Matrix (Fin 3) (Fin 3) R) (h : IsUnit (C 0 0)) :
    ∃ P Q : Matrix (Fin 3) (Fin 3) R,
      IsUnit P.det ∧ IsUnit Q.det ∧ ∃ a b : R,
        rel a b ∧ P * C * Q = Matrix.diagonal ![1, a, b] := by
  obtain ⟨P, Q, hP, hQ, a, b, c, d, hblock⟩ := exists_unit_pivot_reduction C h
  let A : Matrix (Fin 2) (Fin 2) R := !![a, b; c, d]
  obtain ⟨P', Q', hP', hQ', x, y, hxy, heq⟩ := hdiag A
  refine ⟨embedTwo P' * P, Q * embedTwo Q', ?_, ?_, x, y, hxy, ?_⟩
  · rw [Matrix.det_mul, det_embedTwo]
    exact hP'.mul hP
  · rw [Matrix.det_mul, det_embedTwo]
    exact hQ.mul hQ'
  · calc
      (embedTwo P' * P) * C * (Q * embedTwo Q') =
          embedTwo P' * (P * C * Q) * embedTwo Q' := by noncomm_ring
      _ = embedTwo P' * embedTwo A * embedTwo Q' := by rw [hblock]; rfl
      _ = embedTwo (P' * A * Q') := by rw [embedTwo_mul, embedTwo_mul]
      _ = Matrix.diagonal ![1, x, y] := by rw [heq, embedTwo_diagonal]

theorem factorization_of_reduction {n : Type*} [Fintype n] [DecidableEq n]
    (C D P Q : Matrix n n R) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : P * C * Q = D) :
    ∃ U V : Matrix.GeneralLinearGroup n R,
      C = (U : Matrix n n R) * D * (V : Matrix n n R) := by
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det P).2 hP
  obtain ⟨v, rfl⟩ := (Matrix.isUnit_iff_isUnit_det Q).2 hQ
  refine ⟨u⁻¹, v⁻¹, ?_⟩
  rw [← h]
  calc
    C = ((↑u⁻¹ : Matrix n n R) * ↑u) * C * (↑v * ↑v⁻¹) := by simp
    _ = ↑u⁻¹ * (↑u * C * ↑v) * ↑v⁻¹ := by noncomm_ring

theorem exists_factorization_of_two_by_two (rel : R → R → Prop)
    (hdiag : ∀ A : Matrix (Fin 2) (Fin 2) R,
      ∃ P Q : Matrix (Fin 2) (Fin 2) R,
        IsUnit P.det ∧ IsUnit Q.det ∧ ∃ a b : R,
          rel a b ∧ P * A * Q = Matrix.diagonal ![a, b])
    (C : Matrix (Fin 3) (Fin 3) R) (h : IsUnit (C 0 0)) :
    ∃ U V : Matrix.GeneralLinearGroup (Fin 3) R, ∃ a b : R,
      rel a b ∧ C = (U : Matrix (Fin 3) (Fin 3) R) *
        Matrix.diagonal ![1, a, b] * (V : Matrix (Fin 3) (Fin 3) R) := by
  obtain ⟨P, Q, hP, hQ, a, b, hab, heq⟩ :=
    exists_diagonal_of_two_by_two rel hdiag C h
  obtain ⟨U, V, hUV⟩ := factorization_of_reduction C _ P Q hP hQ heq
  exact ⟨U, V, a, b, hab, hUV⟩

theorem exists_factorization_of_two_by_two_units (rel : R → R → Prop)
    (hdiag : ∀ A : Matrix (Fin 2) (Fin 2) R,
      ∃ P Q : Matrix.GeneralLinearGroup (Fin 2) R, ∃ a b : R,
        rel a b ∧ A = (P : Matrix (Fin 2) (Fin 2) R) *
          Matrix.diagonal ![a, b] * (Q : Matrix (Fin 2) (Fin 2) R))
    (C : Matrix (Fin 3) (Fin 3) R) (h : IsUnit (C 0 0)) :
    ∃ U V : Matrix.GeneralLinearGroup (Fin 3) R, ∃ a b : R,
      rel a b ∧ C = (U : Matrix (Fin 3) (Fin 3) R) *
        Matrix.diagonal ![1, a, b] * (V : Matrix (Fin 3) (Fin 3) R) := by
  apply exists_factorization_of_two_by_two rel ?_ C h
  intro A
  obtain ⟨P, Q, a, b, hab, heq⟩ := hdiag A
  refine ⟨↑P⁻¹, ↑Q⁻¹, Matrix.isUnits_det_units P⁻¹,
    Matrix.isUnits_det_units Q⁻¹, a, b, hab, ?_⟩
  rw [heq]
  simp [← Matrix.mul_assoc]

end Problem355.PivotAssembly

end OAI
