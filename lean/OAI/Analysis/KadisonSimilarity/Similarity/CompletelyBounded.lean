import OAI.Analysis.KadisonSimilarity.Representation.Amplification
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace OAI

/-!
# Concrete matrix norms and complete boundedness

The matrix norm used here is `CStarMatrix`'s C-star norm. The representation
on finite Hilbert sums is shown to preserve that norm, connecting the concrete
commutator estimate with the usual notion of complete boundedness.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The algebraic operator-matrix action, before changing the matrix norm. -/
def operatorMatrixRepresentation (n : ℕ) :
    Matrix (Fin n) (Fin n) (H →L[ℂ] H) →⋆ₐ[ℂ]
      (HilbertCopies H n →L[ℂ] HilbertCopies H n) where
  toFun X := matrixOperator X
  map_zero' := by ext ξ i; simp [matrixOperator]
  map_one' := by
    ext ξ i
    simp [matrixOperator, Matrix.one_apply]
    have hentry (j : Fin n) :
        (if i = j then (1 : H →L[ℂ] H) else 0) (ξ j) =
          if i = j then ξ j else 0 := by split_ifs <;> simp
    simp_rw [hentry]
    simp
  map_add' X Y := by ext ξ i; simp [matrixOperator, Finset.sum_add_distrib]
  commutes' c := by
    ext ξ i
    simp [matrixOperator, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
    have hentry (j : Fin n) :
        (if i = j then c • (1 : H →L[ℂ] H) else 0) (ξ j) =
          if i = j then c • ξ j else 0 := by split_ifs <;> simp
    simp_rw [hentry]
    simp
  map_mul' X Y := by
    ext ξ i
    simp only [matrixOperator, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearEquiv.coe_coe,
      PiLp.continuousLinearEquiv_symm_apply, sum_apply, PiLp.proj_apply,
      Matrix.mul_apply, mul_apply_eq_comp, map_sum]
    rw [Finset.sum_comm]
  map_star' X := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro ξ η
    simp only [PiLp.inner_apply, matrixOperator_apply, Matrix.star_apply,
      ContinuousLinearMap.star_eq_adjoint,
      sum_inner, inner_sum, ContinuousLinearMap.adjoint_inner_left]
    rw [Finset.sum_comm]

/-- Operator matrices act as a star algebra homomorphism on the Hilbert sum. -/
def matrixRepresentation (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) →⋆ₐ[ℂ]
      (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
  (operatorMatrixRepresentation n).comp
    (CStarMatrix.ofMatrixStarAlgEquiv.symm :
      CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) ≃⋆ₐ[ℂ]
        Matrix (Fin n) (Fin n) (H →L[ℂ] H)).toStarAlgHom

/-- Every entry can be recovered by evaluating on a vector in one coordinate. -/
theorem operatorMatrixRepresentation_injective (n : ℕ) :
    Function.Injective (operatorMatrixRepresentation (H := H) n) := by
  intro X Y h
  apply Matrix.ext
  intro i j
  ext ξ
  have he := congrArg
    (fun T : HilbertCopies H n →L[ℂ] HilbertCopies H n => T (PiLp.single 2 j ξ) i) h
  simpa [operatorMatrixRepresentation, matrixOperator, PiLp.single_apply, apply_ite] using he

/-- The normed matrix action remains injective after the type synonym is changed. -/
theorem matrixRepresentation_injective (n : ℕ) :
    Function.Injective (matrixRepresentation (H := H) n) :=
  (operatorMatrixRepresentation_injective n).comp CStarMatrix.ofMatrixStarAlgEquiv.symm.injective

/-- The abstract C-star matrix norm equals the concrete Hilbert-space operator norm. -/
theorem norm_matrixOperator_eq (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    ‖matrixOperator (CStarMatrix.ofMatrix.symm X)‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (matrixRepresentation n)
    (matrixRepresentation_injective n) X

section CompletelyBounded

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A uniform bound on all square matrix amplifications, with the C-star
matrix norm on the domain and the Hilbert operator norm on the codomain. -/
def CompleteBound (f : A → (H →L[ℂ] H)) (C : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Matrix (Fin n) (Fin n) A,
    ‖matrixOperator (X.map f)‖ ≤ C * ‖CStarMatrix.ofMatrix X‖

/-- Complete boundedness in terms of the concrete matrix norm. -/
def IsCompletelyBounded (f : A → (H →L[ℂ] H)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ CompleteBound f C

/-- A star representation is completely contractive. -/
theorem completeBound_starHom (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : CompleteBound σ 1 := by
  intro n X
  let σₙ : CStarMatrix (Fin n) (Fin n) A →⋆ₙₐ[ℂ]
      CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H) :=
    CStarMatrix.mapₙₐ σ.toNonUnitalStarAlgHom
  have hn := NonUnitalStarAlgHom.norm_apply_le σₙ (CStarMatrix.ofMatrix X)
  rw [← norm_matrixOperator_eq n] at hn
  change ‖matrixOperator (X.map σ)‖ ≤ ‖CStarMatrix.ofMatrix X‖ at hn
  simpa only [one_mul] using hn

/-- Every inner derivation associated to a star representation is completely
bounded, by twice the norm of its implementer. -/
theorem completeBound_inner (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : H →L[ℂ] H) :
    CompleteBound (fun a => commutator V (σ a)) (2 * ‖V‖) := by
  intro n X
  change ‖matrixOperator (fun i j => commutator V (σ (X i j)))‖ ≤
    (2 * ‖V‖) * ‖CStarMatrix.ofMatrix X‖
  calc
    ‖matrixOperator (fun i j => commutator V (σ (X i j)))‖ =
        ‖commutator (amplify V n) (matrixOperator (X.map σ))‖ :=
      congrArg norm (commutator_amplify_matrixOperator V (X.map σ)).symm
    ‖commutator (amplify V n) (matrixOperator (fun i j => σ (X i j)))‖ ≤
        2 * ‖amplify V n‖ * ‖matrixOperator (fun i j => σ (X i j))‖ :=
      norm_commutator_le _ _
    _ ≤ 2 * ‖V‖ * (1 * ‖CStarMatrix.ofMatrix X‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (norm_amplify_le V n) (by norm_num)
      · exact completeBound_starHom σ n X
      · exact norm_nonneg _
      · positivity
    _ = (2 * ‖V‖) * ‖CStarMatrix.ofMatrix X‖ := by ring

/-- The manuscript's concrete uniform estimate bounds the complete norm of
an inner derivation after any star representation into the tested algebra. -/
theorem completeBound_commutator_of_estimate (P : VonNeumannAlgebra H)
    {C : ℝ} (hC : 0 ≤ C) (estimate : CommutatorEstimate P C)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hσ : ∀ a, σ a ∈ P) (Y : H →L[ℂ] H) :
    CompleteBound (fun a => commutator Y (σ a)) (C * scalarCommutatorNorm P Y) := by
  intro n X
  change ‖matrixOperator (fun i j => commutator Y (σ (X i j)))‖ ≤
    (C * scalarCommutatorNorm P Y) * ‖CStarMatrix.ofMatrix X‖
  calc
    ‖matrixOperator (fun i j => commutator Y (σ (X i j)))‖ =
        ‖commutator (amplify Y n) (matrixOperator (X.map σ))‖ :=
      congrArg norm (commutator_amplify_matrixOperator Y (X.map σ)).symm
    ‖commutator (amplify Y n) (matrixOperator (fun i j => σ (X i j)))‖ ≤
        C * scalarCommutatorNorm P Y * ‖matrixOperator (fun i j => σ (X i j))‖ :=
      estimate Y n _ (fun i j => hσ (X i j))
    _ ≤ C * scalarCommutatorNorm P Y * (1 * ‖CStarMatrix.ofMatrix X‖) :=
      mul_le_mul_of_nonneg_left (completeBound_starHom σ n X)
        (mul_nonneg hC (scalarCommutatorNorm_nonneg P Y))
    _ = (C * scalarCommutatorNorm P Y) * ‖CStarMatrix.ofMatrix X‖ := by ring

/-- The quantitative published Paulsen input, specialized to a single
bounded unital homomorphism. Paulsen, *Completely bounded homomorphisms of
operator algebras* (1984), p. 226. It is an explicit hypothesis interface. -/
def PaulsenSimilarityInput (π : BoundedUnitalHom A H) : Prop :=
  ∀ C : ℝ, 0 ≤ C → CompleteBound π.1 C →
    ∃ S : (H →L[ℂ] H)ˣ,
      ‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖ ≤ C ∧
      ∀ a : A, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
        star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))

end CompletelyBounded

end KadisonSimilarity

end

end OAI
