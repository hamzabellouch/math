import OAI.Analysis.KadisonKastler.AdaptedMatrixRefinement
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace OAI

/-! # Compatible refinement inside a full matrix algebra

Pass to a finite Hilbert-space representation, use the adapted basis, and
transport its rank-one matrix units back. The old signed group is retained.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A ι : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Fintype ι] [DecidableEq ι]

theorem matrixUnits_map_hom (E : Generator.MatrixUnitSystem ι A)
    {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (φ : A →⋆ₐ[ℂ] B) (a : Matrix ι ι ℂ) : (E.map φ).hom a = φ (E.hom a) := by
  simp only [Generator.MatrixUnitSystem.hom_apply, Generator.MatrixUnitSystem.map_entry,
    map_sum, map_smul]

variable [Nontrivial A]

/-- A matrix system in a finite full operator algebra extends to a full
system whose signed group contains the original one. -/
theorem exists_matrix_refinement_of_finite_representation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H] (θ : A ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (E : Generator.MatrixUnitSystem ι A) (o : ι) :
    ∃ (r : ℕ) (F : Generator.MatrixUnitSystem (ι × Fin r) A),
      0 < r ∧ Function.Surjective F.hom ∧
      (∀ i j, ∑ k, F.entry (i, k) (j, k) = E.entry i j) ∧
      matrixSignedGroup E ≤ matrixSignedGroup F := by
  let E' := E.map θ.toStarAlgHom
  let r := Module.finrank ℂ (E'.initialHilbertSpace o)
  let b := stdOrthonormalBasis ℂ (E'.initialHilbertSpace o)
  let Q := Generator.orthonormalMatrixUnits (E'.adaptedBasis o b)
  let F := Q.map θ.symm.toStarAlgHom
  have hfull : Function.Surjective F.hom := by
    intro a
    obtain ⟨x, hx⟩ := Generator.orthonormalMatrixUnits_surjective (E'.adaptedBasis o b) (θ a)
    refine ⟨x, ?_⟩
    rw [matrixUnits_map_hom, hx]
    exact θ.symm_apply_apply a
  have hretain (i j : ι) : ∑ k, F.entry (i, k) (j, k) = E.entry i j := by
    change ∑ k, θ.symm (Q.entry (i, k) (j, k)) = E.entry i j
    rw [← map_sum, adaptedMatrixUnits_retains]
    exact θ.symm_apply_apply _
  have hr : 0 < r := by
    by_contra h
    have hz : r = 0 := Nat.eq_zero_of_not_pos h
    let : IsEmpty (ι × Fin r) := by rw [hz]; infer_instance
    have ht := F.total
    have he : (0 : A) = 1 := by simpa only [Finset.univ_eq_empty, Finset.sum_empty] using ht
    exact zero_ne_one he
  exact ⟨r, F, hr, hfull, hretain, matrixSignedGroup_refinement E F hretain⟩

/-- The only representation data needed above are supplied by any full
matrix system for the containing algebra. -/
theorem exists_matrix_refinement_in_full_matrix_algebra
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Generator.MatrixUnitSystem κ A) (hP : Function.Surjective P.hom)
    (E : Generator.MatrixUnitSystem ι A) (o : ι) :
    ∃ (r : ℕ) (F : Generator.MatrixUnitSystem (ι × Fin r) A),
      0 < r ∧ Function.Surjective F.hom ∧
      (∀ i j, ∑ k, F.entry (i, k) (j, k) = E.entry i j) ∧
      matrixSignedGroup E ≤ matrixSignedGroup F := by
  let θ₀ : Matrix κ κ ℂ ≃⋆ₐ[ℂ] A :=
    StarAlgEquiv.ofBijective P.hom ⟨P.injective, hP⟩
  let θ := θ₀.symm.trans (Matrix.toEuclideanCLM (𝕜 := ℂ))
  exact exists_matrix_refinement_of_finite_representation θ E o

end

end KadisonKastler

end OAI
