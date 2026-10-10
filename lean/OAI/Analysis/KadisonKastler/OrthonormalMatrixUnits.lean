import OAI.Analysis.KadisonKastler.FiniteMatrixUnitBasis

namespace OAI

/-! # Full matrix units from a finite orthonormal basis -/

open scoped BigOperators

noncomputable section

namespace Generator

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

/-- The rank-one matrix units associated with an orthonormal basis. -/
def orthonormalMatrixUnits (b : OrthonormalBasis ι ℂ H) : MatrixUnitSystem ι (H →L[ℂ] H) where
  entry i j := InnerProductSpace.rankOne ℂ (b i) (b j)
  star_entry i j := by
    rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]
  mul_entry i j k l := by
    change (InnerProductSpace.rankOne ℂ (b i) (b j)).comp
      (InnerProductSpace.rankOne ℂ (b k) (b l)) = _
    rw [InnerProductSpace.rankOne_comp_rankOne, b.inner_eq_ite]
    split_ifs <;> simp_all
  total := b.sum_rankOne_eq_id

@[simp]
theorem orthonormalMatrixUnits_entry_apply (b : OrthonormalBasis ι ℂ H)
    (i j : ι) (x : H) :
    (orthonormalMatrixUnits b).entry i j x = inner ℂ (b j) x • b i := rfl

/-- These matrix units span all bounded operators on the finite Hilbert space. -/
theorem orthonormalMatrixUnits_surjective (b : OrthonormalBasis ι ℂ H) :
    Function.Surjective (orthonormalMatrixUnits b).hom := by
  intro T
  let a : Matrix ι ι ℂ := fun i j => inner ℂ (b i) (T (b j))
  refine ⟨a, ?_⟩
  have hb (j : ι) : (orthonormalMatrixUnits b).hom a (b j) = T (b j) := by
    calc
      _ = ∑ i, inner ℂ (b i) (T (b j)) • b i := by
        change (∑ i, ∑ k, a i k • InnerProductSpace.rankOne ℂ (b i) (b k)) (b j) = _
        simp only [sum_apply, smul_apply, InnerProductSpace.rankOne_apply,
          b.inner_eq_ite, smul_smul]
        simp [a, mul_ite, ite_smul]
      _ = _ := b.sum_repr' _
  apply ContinuousLinearMap.ext
  intro x
  rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, hb]

end Generator

end

end OAI
