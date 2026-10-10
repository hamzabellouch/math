import OAI.GroupTheory.PolycyclicRecognition.Geometry.TruncatedWordExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairedWordCoproduct

namespace OAI

/-! # Primitive rational coefficients of the truncated universal logarithm -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable (c n : ℕ)

theorem pairedWordCoproduct_eq_truncated (p : TruncatedWords c n) :
    pairedWordCoproduct (TruncatedRationalScalars c) n p =
      monoidTensorCoordinates (TruncatedRationalScalars c) _ _ (truncatedWordCoproduct c n p) := by
  change pairedWordCoproduct (TruncatedRationalScalars c) n p =
    ((monoidTensorCoordinates (TruncatedRationalScalars c) _ _).comp
      (truncatedWordCoproduct c n)) p
  apply congrArg (fun F : TruncatedWords c n →ₐ[TruncatedRationalScalars c] _ => F p)
  apply MonoidAlgebra.algHom_ext'
  · apply FreeMonoid.hom_eq
    intro i
    change pairedWordCoproduct (TruncatedRationalScalars c) n (truncatedWordLetter c n i) =
      monoidTensorCoordinates (TruncatedRationalScalars c) _ _
        (truncatedWordCoproduct c n (truncatedWordLetter c n i))
    rw [truncatedWordCoproduct_letter, map_add]
    simp only [truncatedWordLetter, pairedWordCoproduct_letter, MonoidAlgebra.one_def,
      monoidTensorCoordinates_single, one_mul]
  · exact Subsingleton.elim _ _

theorem primitive_truncated_coefficient (f : TruncatedRationalScalars c →ₗ[ℚ] ℚ)
    (p : TruncatedWords c n)
    (hp : truncatedWordCoproduct c n p =
      p ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
        (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] p) :
    IsPrimitiveRationalWord (monoidCoefficientLinear f p) := by
  have h := congrArg (monoidTensorCoordinates (TruncatedRationalScalars c) _ _) hp
  rw [← pairedWordCoproduct_eq_truncated, map_add, monoidTensorCoordinates_tmul_one,
    monoidTensorCoordinates_one_tmul] at h
  have h' := congrArg (monoidCoefficientLinear f) h
  rw [coefficientLinear_pairedWordCoproduct, map_add, monoidCoefficientLinear_mapDomain,
    monoidCoefficientLinear_mapDomain] at h'
  unfold IsPrimitiveRationalWord
  apply monoidTensorCoordinates_injective ℚ (FreeMonoid (Fin n)) (FreeMonoid (Fin n))
  rw [← pairedWordCoproduct_eq_rational, map_add, monoidTensorCoordinates_tmul_one,
    monoidTensorCoordinates_one_tmul]
  exact h'

def universalLogarithmCoefficient (d : ℕ) : RationalWords n :=
  monoidCoefficientLinear (truncatedScalarCoefficient c d) (truncatedWordLogarithm c n)

theorem universalLogarithmCoefficient_primitive (d : ℕ) :
    IsPrimitiveRationalWord (universalLogarithmCoefficient c n d) :=
  primitive_truncated_coefficient c n _ _ (truncatedWordLogarithm_primitive c n)

end PolycyclicRecognition

end

end OAI
