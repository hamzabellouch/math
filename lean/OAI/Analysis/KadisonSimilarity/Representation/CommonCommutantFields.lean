import OAI.Analysis.KadisonSimilarity.Representation.CommonSpectralCommutant
import OAI.Analysis.KadisonSimilarity.Derivation.DiagonalMatrixNorm
import OAI.Analysis.KadisonSimilarity.Tracial.IsometricMatrixExtension
import OAI.Analysis.KadisonSimilarity.Representation.ScalarHilbertSeparability

namespace OAI

/-! Every member of the original abelian commutant has an actual operator
field over the common spectral measure. The construction retains its norm
and its algebraic operations almost everywhere. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

variable {A H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace H] in
theorem commutant_commutes_representation
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra) (a : A) :
    (T : H →L[ℂ] H) * π a = π a * T := by
  have ht : (T : H →L[ℂ] H) ∈ starSubalgebraCommutant π.range := T.property
  rw [← SetLike.mem_coe, coe_starSubalgebraCommutant] at ht
  exact (ht (π a) ⟨a, rfl⟩).symm

def commonCommutantField
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra) :
    WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators :=
  diagonalField (cyclicCommonBaseMeasure π D)
    (isometricExtension (cyclicCommonEmbedding π D) T)
    (commonExtension_commutes_localizations π D T (commutant_commutes_representation π T))

theorem commonCommutantField_action
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra)
    (f : CommonCyclicHilbert π D) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      isometricExtension (cyclicCommonEmbedding π D) T f x = commonCommutantField π D T x (f x) :=
  diagonalField_action (cyclicCommonBaseMeasure π D) _ _ f

theorem commonCommutantField_norm_iff
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra) (C : ℝ) (hC : 0 ≤ C) :
    ‖(T : H →L[ℂ] H)‖ ≤ C ↔
      ∀ᵐ x ∂cyclicCommonBaseMeasure π D, ‖commonCommutantField π D T x‖ ≤ C := by
  rw [← isometricExtension_norm (cyclicCommonEmbedding π D) T]
  exact pointwise_field_norm_iff (cyclicCommonBaseMeasure π D) _ _
    (commonCommutantField_action π D T) C hC

theorem commonCommutantField_add
    (T U : (starSubalgebraCommutant π.range).toStarSubalgebra) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      commonCommutantField π D (T + U) x =
        commonCommutantField π D T x + commonCommutantField π D U x := by
  apply pointwise_field_add (cyclicCommonBaseMeasure π D) _ _ _ _ _
    (commonCommutantField_action π D T) (commonCommutantField_action π D U)
  have h := commonCommutantField_action π D (T + U)
  change ∀ f : CommonCyclicHilbert π D, ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
    isometricExtension (cyclicCommonEmbedding π D)
      ((T : H →L[ℂ] H) + (U : H →L[ℂ] H)) f x = _ at h
  simpa only [isometricExtension_add] using h

theorem commonCommutantField_sub
    (T U : (starSubalgebraCommutant π.range).toStarSubalgebra) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      commonCommutantField π D (T - U) x =
        commonCommutantField π D T x - commonCommutantField π D U x := by
  apply ae_operator_eq_of_forall_vectors (cyclicCommonBaseMeasure π D)
  intro v
  have hT := pointwise_action_column (cyclicCommonBaseMeasure π D) _ _
    (commonCommutantField_action π D T) v
  have hU := pointwise_action_column (cyclicCommonBaseMeasure π D) _ _
    (commonCommutantField_action π D U) v
  have hsub := pointwise_action_column (cyclicCommonBaseMeasure π D) _ _
    (commonCommutantField_action π D (T - U)) v
  change ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
    isometricExtension (cyclicCommonEmbedding π D)
      ((T : H →L[ℂ] H) - (U : H →L[ℂ] H)) (Lp.const 2 _ v) x = _ at hsub
  rw [isometricExtension_sub] at hsub
  filter_upwards [hT, hU, hsub,
    Lp.coeFn_sub
      (isometricExtension (cyclicCommonEmbedding π D) T (Lp.const 2 _ v))
      (isometricExtension (cyclicCommonEmbedding π D) U (Lp.const 2 _ v))]
    with x ht hu htu hs
  simpa only [sub_apply, hs, Pi.sub_apply, ht, hu] using htu.symm

theorem commonCommutantField_mul
    (T U : (starSubalgebraCommutant π.range).toStarSubalgebra) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      commonCommutantField π D (T * U) x =
        commonCommutantField π D T x * commonCommutantField π D U x := by
  apply pointwise_field_mul (cyclicCommonBaseMeasure π D) _ _ _ _ _
    (commonCommutantField_action π D T) (commonCommutantField_action π D U)
  have h := commonCommutantField_action π D (T * U)
  change ∀ f : CommonCyclicHilbert π D, ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
    isometricExtension (cyclicCommonEmbedding π D)
      ((T : H →L[ℂ] H) * (U : H →L[ℂ] H)) f x = _ at h
  simpa only [isometricExtension_mul] using h

theorem commonCommutantField_matrix_norm_iff {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (starSubalgebraCommutant π.range).toStarSubalgebra)
    (C : ℝ) (hC : 0 ≤ C) :
    ‖matrixOperator (fun i j => (X i j : H →L[ℂ] H))‖ ≤ C ↔
      ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
        ‖matrixOperator (fun i j => commonCommutantField π D (X i j) x)‖ ≤ C := by
  rw [← norm_matrix_isometricExtension (cyclicCommonEmbedding π D)
    (fun i j => (X i j : H →L[ℂ] H))]
  exact diagonal_matrix_norm_iff (cyclicCommonBaseMeasure π D) _
    (fun x i j => commonCommutantField π D (X i j) x)
    (fun i j => commonCommutantField_action π D (X i j)) C hC

end KadisonSimilarity

end

end OAI
