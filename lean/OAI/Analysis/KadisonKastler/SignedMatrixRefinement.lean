import OAI.Analysis.KadisonKastler.MatrixAveraging

namespace OAI

/-! # Compatible finite signed groups under matrix refinement

Keeping the first matrix coordinates as sums over the new coordinates keeps
the old signed-permutation group inside the new finite group.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A ι κ : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The finite subgroup actually represented by the matrix units. -/
def matrixSignedGroup (E : Generator.MatrixUnitSystem ι A) : Subgroup (unitary A) :=
  (matrixUnitSignedRepresentation E).range

instance matrixSignedGroup_finite (E : Generator.MatrixUnitSystem ι A) :
    Finite (matrixSignedGroup E) := (Set.finite_range _).to_subtype

theorem signedRepresentation_diagonal (E : Generator.MatrixUnitSystem ι A) (d : ι → ℤˣ) :
    (matrixUnitSignedRepresentation E (SemidirectProduct.inl d) : A) =
      ∑ i, ((d i : ℤ) : ℂ) • E.entry i i := by
  rw [matrixUnitSignedRepresentation_inl]
  simp [Generator.MatrixUnitSystem.hom_apply, signDiagonal, Matrix.diagonal, ite_smul]

theorem signedRepresentation_permutation (E : Generator.MatrixUnitSystem ι A)
    (σ : Equiv.Perm ι) :
    (matrixUnitSignedRepresentation E (SemidirectProduct.inr σ) : A) =
      ∑ i, E.entry (σ i) i := by
  rw [matrixUnitSignedRepresentation_inr]
  simp only [Generator.MatrixUnitSystem.hom_apply, permutationMatrix_apply,
    ite_smul, one_smul, zero_smul]
  rw [Finset.sum_comm]
  simp

variable (E : Generator.MatrixUnitSystem ι A) (F : Generator.MatrixUnitSystem (ι × κ) A)
  (hretain : ∀ i j, ∑ k, F.entry (i, k) (j, k) = E.entry i j)

include hretain in
theorem signedDiagonal_refinement (d : ι → ℤˣ) :
    (matrixUnitSignedRepresentation F (SemidirectProduct.inl (fun p : ι × κ => d p.1)) : A) =
      matrixUnitSignedRepresentation E (SemidirectProduct.inl d) := by
  rw [signedRepresentation_diagonal, signedRepresentation_diagonal, Fintype.sum_prod_type]
  simp_rw [← Finset.smul_sum, hretain]

include hretain in
theorem signedPermutation_refinement (σ : Equiv.Perm ι) :
    (matrixUnitSignedRepresentation F
      (SemidirectProduct.inr (σ.prodCongr (Equiv.refl κ))) : A) =
      matrixUnitSignedRepresentation E (SemidirectProduct.inr σ) := by
  rw [signedRepresentation_permutation, signedRepresentation_permutation,
    Fintype.sum_prod_type]
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, hretain]

include hretain in
/-- Every old signed unitary is a new signed unitary after compatible refinement. -/
theorem matrixSignedGroup_refinement : matrixSignedGroup E ≤ matrixSignedGroup F := by
  rintro u ⟨g, rfl⟩
  let g' : SignedPermutation (ι × κ) :=
    SemidirectProduct.inl (fun p => g.left p.1) *
      SemidirectProduct.inr (g.right.prodCongr (Equiv.refl κ))
  refine ⟨g', ?_⟩
  apply Subtype.ext
  rw [show g' = SemidirectProduct.inl (fun p => g.left p.1) *
      SemidirectProduct.inr (g.right.prodCongr (Equiv.refl κ)) from rfl, map_mul]
  change (matrixUnitSignedRepresentation F (SemidirectProduct.inl (fun p => g.left p.1)) : A) *
      (matrixUnitSignedRepresentation F
        (SemidirectProduct.inr (g.right.prodCongr (Equiv.refl κ))) : A) = _
  rw [signedDiagonal_refinement E F hretain, signedPermutation_refinement E F hretain,
    ← Submonoid.coe_mul, ← map_mul]
  congr 2
  exact SemidirectProduct.inl_left_mul_inr_right g

end

end KadisonKastler

end OAI
