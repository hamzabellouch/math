import OAI.Analysis.KadisonSimilarity.Tracial.MatrixSmallCorner
import OAI.Analysis.KadisonSimilarity.Representation.FiniteAmplificationReduction

namespace OAI

/-! Exact recovery of finite matrix commutators from the normalized matrix
GNS space. The surjective linear isometry transports the represented
operators and preserves their commutator norms. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The matrix left action is the represented matrix for the actual
amplified scalar GNS representation. -/
theorem matrixLeftArray_eq_representedMatrix (τ : A →ₚ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    matrixLeftArray τ X =
      representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom n) X := rfl

/-- The normalized matrix GNS identification preserves the full commutator
norm, rather than only one inequality. -/
theorem norm_matrixGNSLiftOperator_commutator (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (matrixGNSLiftOperator τ Y)
      ((normalizedMatrixTrace τ n).gnsStarAlgHom X)‖ =
      ‖commutator (amplify Y n) (matrixLeftArray τ X)‖ := by
  let U := matrixGNSUnitary τ n
  let T := commutator (matrixGNSLiftOperator τ Y)
    ((normalizedMatrixTrace τ n).gnsStarAlgHom X)
  have he : U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      commutator (amplify Y n) (matrixLeftArray τ X) := by
    apply ContinuousLinearMap.ext
    intro ξ
    change U (T (U.symm ξ)) = _
    rw [matrixGNSLiftOperator_commutator, LinearIsometryEquiv.apply_symm_apply]
  calc
    _ = ‖T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
      (norm_comp_isometricCoordinates T U.symm).symm
    _ = ‖U.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ :=
      (norm_isometricCoordinates_comp _ U).symm
    _ = _ := congrArg norm he

/-- The same equality in the notation used by finite amplification. -/
theorem norm_matrixGNSLiftOperator_commutator_represented (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖commutator (matrixGNSLiftOperator τ Y)
      ((normalizedMatrixTrace τ n).gnsStarAlgHom X)‖ =
      ‖commutator (amplify Y n)
        (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom n) X)‖ :=
  norm_matrixGNSLiftOperator_commutator τ Y X

/-- A centered-symmetry estimate on the actual matrix GNS space transfers
with precisely the same constant to the square Hilbert array. -/
theorem matrixGNS_centered_symmetry_bound_transfer (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n) {B : ℝ}
    (hbound : ∀ S : CStarMatrix (Fin n) (Fin n) A,
      star S = S → S * S = 1 → normalizedMatrixTrace τ n S = 0 →
      ‖commutator (matrixGNSLiftOperator τ Y)
        ((normalizedMatrixTrace τ n).gnsStarAlgHom S)‖ ≤ B)
    (S : CStarMatrix (Fin n) (Fin n) A)
    (hstar : star S = S) (hsq : S * S = 1) (htrace : normalizedMatrixTrace τ n S = 0) :
    ‖commutator (amplify Y n)
      (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom n) S)‖ ≤ B := by
  rw [← norm_matrixGNSLiftOperator_commutator_represented]
  exact hbound S hstar hsq htrace

/-- A bound on the single actual dilated symmetry in normalized matrix GNS
recovers the original finite matrix test after the multiplicity replacement. -/
theorem finite_amplification_bound_of_matrixGNS_symmetry {r h : ℕ}
    (τ : A →ₚ[ℂ] ℂ) (e : Fin r ↪ Fin (4 * n)) (f : Fin h ↪ Fin n)
    (Y : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
    (X : CStarMatrix (Fin h) (Fin h) A) (hX : ‖X‖ ≤ 1)
    (Y₀ : HilbertCopies τ.GNS (4 * n) →L[ℂ] HilbertCopies τ.GNS (4 * n))
    {η B : ℝ} (hclose : ‖Y₀ - padArrayOperator e Y‖ ≤ η)
    (hbound : ‖commutator (matrixGNSLiftOperator τ Y₀)
      ((normalizedMatrixTrace τ (4 * n)).gnsStarAlgHom
        (fourfoldMatrixFlatten n (contractionSymmetryUnitary (cstarMatrixPadding f X)
          (by simpa only [norm_cstarMatrixPadding] using hX))))‖ ≤ B) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
      B + 2 * η := by
  apply finite_amplification_bound_of_multiplicity_approximation
    τ.gnsStarAlgHom e f Y X hX Y₀ hclose
  rw [← norm_matrixGNSLiftOperator_commutator_represented]
  exact hbound

/-- Only selfadjoint square-one centered elements are needed on the matrix
GNS side; all other tests are supplied by the concrete dilation. -/
theorem finite_amplification_bound_of_matrixGNS_centered_tests {r h : ℕ}
    (τ : A →ₚ[ℂ] ℂ) (e : Fin r ↪ Fin (4 * n)) (f : Fin h ↪ Fin n)
    (Y : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
    (X : CStarMatrix (Fin h) (Fin h) A) (hX : ‖X‖ ≤ 1)
    (Y₀ : HilbertCopies τ.GNS (4 * n) →L[ℂ] HilbertCopies τ.GNS (4 * n))
    {η B : ℝ} (hclose : ‖Y₀ - padArrayOperator e Y‖ ≤ η)
    (hbound : ∀ S : CStarMatrix (Fin (4 * n)) (Fin (4 * n)) A,
      star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * n) S = 0 →
      ‖commutator (matrixGNSLiftOperator τ Y₀)
        ((normalizedMatrixTrace τ (4 * n)).gnsStarAlgHom S)‖ ≤ B) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
      B + 2 * η := by
  apply finite_amplification_bound_of_matrixGNS_symmetry τ e f Y X hX Y₀ hclose
  obtain ⟨hstar, hsquare, htrace⟩ := padded_flattened_symmetry_properties τ f X hX
  exact hbound _ hstar hsquare htrace

omit [NeZero n] in
/-- Uniform replacements on square matrix GNS spaces control every finite
standard multiplicity and every matrix size. Normalization of arbitrary
tests, dimension padding, and the two approximation errors are all handled
by the proved dilation reduction. -/
theorem finite_standard_bound_of_matrixGNS_replacements {r : ℕ}
    (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r) {η B : ℝ}
    (hconstant : 0 ≤ B + 2 * η)
    (hreplace : ∀ (m : ℕ) [NeZero m], ∀ e : Fin r ↪ Fin (4 * m),
      ∃ Y₀ : HilbertCopies τ.GNS (4 * m) →L[ℂ] HilbertCopies τ.GNS (4 * m),
        ‖Y₀ - padArrayOperator e Y‖ ≤ η ∧
        ∀ S : CStarMatrix (Fin (4 * m)) (Fin (4 * m)) A,
          star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * m) S = 0 →
          ‖commutator (matrixGNSLiftOperator τ Y₀)
            ((normalizedMatrixTrace τ (4 * m)).gnsStarAlgHom S)‖ ≤ B)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) A) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
      (B + 2 * η) * ‖X‖ := by
  apply finite_amplification_bound_of_centered_tests τ.gnsStarAlgHom τ Y hconstant
  intro m _ e
  obtain ⟨Y₀, hclose, hbound⟩ := hreplace m e
  refine ⟨amplify Y₀ (4 * m),
    (norm_amplify_sub_le Y₀ (padArrayOperator e Y) (4 * m)).trans hclose, ?_⟩
  intro S hstar hsquare htrace
  rw [← norm_matrixGNSLiftOperator_commutator_represented]
  exact hbound S hstar hsquare htrace

end KadisonSimilarity

end

end OAI
