import Mathlib

namespace OAI

noncomputable section

namespace Problem335

open Module Submodule

universe u v w x

/-- Comparing all finite column families compares matrix ranks. -/
theorem matrix_rank_le_of_independent_imp
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {K : Type w} {L : Type x} [Field K] [Field L]
    (A : Matrix m n K) (B : Matrix m n L)
    (h : ∀ (r : ℕ) (f : Fin r → n), LinearIndependent K (A.col ∘ f) →
      LinearIndependent L (B.col ∘ f)) : A.rank ≤ B.rank := by
  classical
  obtain ⟨p, hp, hspan, hli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
  choose f hf using hp
  have heq : A.col ∘ f = p := funext hf
  have hli' : LinearIndependent L (B.col ∘ f) := h _ f (heq.symm ▸ hli)
  rw [A.rank_eq_finrank_span_cols, B.rank_eq_finrank_span_cols]
  have hsub : Set.range (B.col ∘ f) ⊆ Set.range B.col := by
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, rfl⟩
  calc
    finrank K (span K (Set.range A.col)) =
      finrank L (span L (Set.range (B.col ∘ f))) := by
        simp [finrank_span_eq_card hli']
    _ ≤ finrank L (span L (Set.range B.col)) :=
      Submodule.finrank_mono (Submodule.span_mono hsub)

/-- Matrices with the same finite-column dependence relations have equal ranks. -/
theorem matrix_rank_eq_of_independent_iff
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {K : Type w} {L : Type x} [Field K] [Field L]
    (A : Matrix m n K) (B : Matrix m n L)
    (h : ∀ (r : ℕ) (f : Fin r → n), LinearIndependent K (A.col ∘ f) ↔
      LinearIndependent L (B.col ∘ f)) : A.rank = B.rank := by
  exact le_antisymm
    (matrix_rank_le_of_independent_imp A B (fun r f => (h r f).mp))
    (matrix_rank_le_of_independent_imp B A (fun r f => (h r f).mpr))

/-- Extending an integral coefficient matrix to either of two faithful field
extensions gives the same rank. The fields need not embed into each other. -/
theorem matrix_rank_algebraMap_eq
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {R K L : Type*} [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra R L] [FaithfulSMul R K] [FaithfulSMul R L]
    (A : Matrix m n R) :
    (A.map (algebraMap R K)).rank = (A.map (algebraMap R L)).rank := by
  apply matrix_rank_eq_of_independent_iff
  intro r f
  change LinearIndependent K (fun i => algebraMap R K ∘ A.col (f i)) ↔
    LinearIndependent L (fun i => algebraMap R L ∘ A.col (f i))
  rw [linearIndependent_algebraMap_comp_iff, linearIndependent_algebraMap_comp_iff]

/-- A field embedding preserves the rank of a finite rectangular matrix. -/
theorem matrix_rank_map
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    {F K : Type*} [Field F] [Field K] (f : F →+* K) (A : Matrix m n F) :
    (A.map f).rank = A.rank := by
  let : Algebra F K := f.toAlgebra
  simpa only [RingHom.algebraMap_toAlgebra, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] using (matrix_rank_algebraMap_eq (K := K) (L := F) A)

/-- Integer matrices have the same rank over any two characteristic-zero fields. -/
theorem integer_matrix_rank_eq
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (K L : Type*) [Field K] [CharZero K] [Field L] [CharZero L]
    (A : Matrix m n ℤ) :
    (A.map (Int.castRingHom K)).rank = (A.map (Int.castRingHom L)).rank := by
  exact matrix_rank_algebraMap_eq A

/-- The characteristic-zero rank-transfer step used in the lower bound. -/
theorem integer_matrix_rank_eq_complex
    {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (K : Type*) [Field K] [CharZero K] (A : Matrix m n ℤ) :
    (A.map (Int.castRingHom K)).rank = (A.map (Int.castRingHom ℂ)).rank := by
  exact integer_matrix_rank_eq K ℂ A

end Problem335

end

end OAI
