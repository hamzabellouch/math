import OAI.Algebra.OddKaplansky.FreeShiftCount

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4

section
namespace OddKaplansky.WeightedGram
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {X : Type portUniverse2} {I : Type portUniverse3} [Field K] [Fintype X] [sectionInstance20 : Fintype I] [sectionInstance19 : DecidableEq X] [sectionInstance21 : DecidableEq I]

lemma exists_minor
    {K : Type contextUniverse1}
    {X : Type contextUniverse2}
    {I : Type contextUniverse3}
    [Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} X]
    [Fintype.{contextUniverse3} I]
    [DecidableEq.{contextUniverse2 + 1} X]
    [DecidableEq.{contextUniverse3 + 1} I] (B : Matrix X I K) (hB : LinearIndependent K B.col) :
    ∃ f : I ↪ X, (B.submatrix f id).det ≠ 0 := by
  have hr : B.rank = Fintype.card I := by
    rw [← B.rank_transpose]
    exact hB.rank_matrix
  have ht : Submodule.span K (Set.range B.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← B.rank_eq_finrank_span_row, hr, Module.finrank_pi]
  let b := Module.Basis.ofSpan ht.ge
  let e := b.indexEquiv (Pi.basisFun K I)
  let b' := b.reindex e
  have hb (i : I) : ∃ x, B.row x = b' i := by
    exact Module.Basis.ofSpan_subset ht.ge ⟨e.symm i, (Module.Basis.reindex_apply b e i).symm⟩
  choose f hf using hb
  have hfi : Function.Injective f := by
    intro i j hij
    apply b'.injective
    rw [← hf, ← hf, hij]
  refine ⟨⟨f,hfi⟩, Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.linearIndependent_row_iff.mp ?_)⟩
  change LinearIndependent K (fun i => B.row (f i))
  have he : (fun i => B.row (f i)) = b' := funext hf
  rw [he]
  exact b'.linearIndependent

lemma gram_entry
    {X : Type contextUniverse1}
    {I : Type contextUniverse2}
    [Fintype.{contextUniverse1} X]
    [Fintype.{contextUniverse2} I]
    [DecidableEq.{contextUniverse1 + 1} X]
    [DecidableEq.{contextUniverse2 + 1} I] {A : Type portUniverse4} [CommRing A] (B : Matrix X I A) (τ : X → A) (i j : I) :
    (B.transpose * Matrix.diagonal τ * B) i j = ∑ x : X, B x i * τ x * B x j := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

def polynomial (B : Matrix X I K) : MvPolynomial X K :=
  ((B.transpose.map (MvPolynomial.C : K →+* MvPolynomial X K)) * Matrix.diagonal (fun x => (MvPolynomial.X x : MvPolynomial X K)) *
    B.map (MvPolynomial.C : K →+* MvPolynomial X K)).det

lemma eval_polynomial (B : Matrix X I K) (τ : X → K) :
    MvPolynomial.eval τ (polynomial B) = (B.transpose * Matrix.diagonal τ * B).det := by
  rw [polynomial, (MvPolynomial.eval τ).map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply]

lemma nonzero (B : Matrix X I K) (hB : LinearIndependent K B.col) : polynomial B ≠ 0 := by
  obtain ⟨f,hf⟩ := exists_minor B hB
  let τ : X → K := fun x => if x ∈ Set.range f then 1 else 0
  have he : B.transpose * Matrix.diagonal τ * B = (B.submatrix f id).transpose * (B.submatrix f id) := by
    apply Matrix.ext
    intro i j
    rw [gram_entry]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
    calc
      _ = ∑ x ∈ Finset.univ.image f, B x i * τ x * B x j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hx
        have hx' : x ∉ Set.range f := by simpa using hx
        simp only [τ, ite_eq_right hx', mul_zero, zero_mul]
      _ = ∑ k : I, B (f k) i * B (f k) j := by
        rw [Finset.sum_image f.injective.injOn]
        simp [τ]
  intro hz
  have hh := eval_polynomial B τ
  rw [hz,map_zero,he,Matrix.det_mul,Matrix.det_transpose] at hh
  exact (mul_ne_zero hf hf) hh.symm

lemma totalDegree (B : Matrix X I K) : (polynomial B).totalDegree ≤ Fintype.card I := by
  unfold polynomial
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hc : (↑(Equiv.Perm.sign σ) : MvPolynomial X K).totalDegree = 0 := by
    simpa using (MvPolynomial.totalDegree_C (Equiv.Perm.sign σ : K))
  rw [hc,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : I, 1 := by
      apply Finset.sum_le_sum
      intro i _
      change (( (B.map (MvPolynomial.C : K →+* MvPolynomial X K)).transpose *
        Matrix.diagonal (fun x => (MvPolynomial.X x : MvPolynomial X K)) * B.map (MvPolynomial.C : K →+* MvPolynomial X K)) (σ i) i).totalDegree ≤ 1
      rw [gram_entry]
      simp only [Matrix.map_apply]
      apply MvPolynomial.totalDegree_finsetSum_le
      intro x _
      exact (MvPolynomial.totalDegree_mul _ _).trans (by
        have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (B x (σ i))) (MvPolynomial.X x : MvPolynomial X K)
        simpa using h)
    _ = Fintype.card I := by simp

end
end OddKaplansky.WeightedGram

end

end OAI
