import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialAffineDegree

namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

def reindexIdentity (N : I → ℕ) : ResidueBoxSlice N 1 where
  start _ := 0
  length := N
  inside _ _ hj := by simpa using hj

def reindexComp (S : ResidueBoxSlice N q) {r : ℕ} (T : ResidueBoxSlice S.length r) :
    ResidueBoxSlice N (q * r) where
  start i := S.start i + q * T.start i
  length := T.length
  inside i j hj := by
    have h := S.inside i (T.start i + r * j) (T.inside i j hj)
    simpa only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using h

@[simp] theorem reindexComp_point (S : ResidueBoxSlice N q) {r : ℕ}
    (T : ResidueBoxSlice S.length r) (x : ∀ i, Fin (T.length i)) :
    (S.reindexComp T).point x = S.point (T.point x) := by
  ext i
  simp [reindexComp, point, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

noncomputable def reindexPolynomial (S : ResidueBoxSlice N q) (i : I) : MvPolynomial I ℝ :=
  MvPolynomial.C (S.start i : ℝ) + MvPolynomial.C (q : ℝ) * MvPolynomial.X i

theorem reindexPolynomial_degree (S : ResidueBoxSlice N q) (i : I) :
    (S.reindexPolynomial i).totalDegree ≤ 1 := by
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le
    ((MvPolynomial.totalDegree_C _).trans_le (by omega))
    ((MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add,
        le_refl])))

@[simp] theorem reindexPolynomial_eval (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) (i : I) :
    MvPolynomial.aeval (R := ℝ) (fun i => ((x i).val : ℝ)) (S.reindexPolynomial i) =
      ((S.point x i).val : ℝ) := by
  simp [reindexPolynomial, point, Nat.cast_add, Nat.cast_mul]

end ResidueBoxSlice

namespace VectorPolynomial

theorem coefficients_reindex_substitute_mem {I K V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : Submodule ℝ V) (f : I → MvPolynomial K ℝ) (p : VectorPolynomial I ℝ V)
    (hp : ∀ α, coefficients p α ∈ W) :
    ∀ α, coefficients (substitute f p) α ∈ W := by
  intro α
  rw [coefficients_substitute]
  exact W.sum_mem (fun β _ => W.smul_mem _ (hp β))

theorem eval_reindex_slice_substitute {I V : Type*} [AddCommGroup V] [Module ℝ V]
    {N : I → ℕ} {q : ℕ} (S : ResidueBoxSlice N q) (p : VectorPolynomial I ℝ V)
    (x : ∀ i, Fin (S.length i)) :
    eval (fun i => ((x i).val : ℝ)) (substitute S.reindexPolynomial p) =
      eval (fun i => ((S.point x i).val : ℝ)) p := by
  simp only [eval_substitute, ResidueBoxSlice.reindexPolynomial_eval]

end VectorPolynomial
end Erdos3

end

end OAI
