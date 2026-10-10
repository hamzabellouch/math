import OAI.Analysis.Pureness.States.NormalizedMatrixStateDiagonal
import OAI.Analysis.Pureness.States.OriginalScalarNuclearQuasitrace
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientIteration
import OAI.Analysis.Pureness.Cuntz.FinOneMatrixTransport
import OAI.Analysis.Pureness.States.RegularizedStateFreeGroupExactness

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped NNReal ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A))
variable (hy : y ≠ 0) (f : StateSpace y) (V : Ultrafilter ℕ)

instance matrixStateAWNontrivial : Nontrivial (NormalizedMatrixStateUltraAW hsimple y hy f V) :=
  Function.Injective.nontrivial (matrixStateDiagonalAWEmbedding_injective hsimple y hy f V)

abbrev matrixStateUltralimitPositive :=
  ultralimitPositiveQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) V
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)

abbrev matrixStateUltralimitTriangle :=
  ultralimitPositiveQuasitrace_metricSize_add
    (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) V
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)

abbrev matrixStateUltralimitSqrt :=
  ultralimitPositiveQuasitrace_sqrt_add
    (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) V
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)

abbrev matrixStateAWPositive :=
  (matrixStateUltralimitPositive hsimple y hy f V).quotientPositiveQuasitrace
    (matrixStateUltralimitTriangle hsimple y hy f V)
    (matrixStateUltralimitSqrt hsimple y hy f V)

lemma matrixStateAWPositive_complex (x : NormalizedMatrixStateUltraAW hsimple y hy f V) :
    (matrixStateAWPositive hsimple y hy f V).complexValue x =
      matrixStateAWQuasitrace hsimple y hy f V x :=
  rfl

abbrev matrixStateAWPositive_triangle :=
  (matrixStateUltralimitPositive hsimple y hy f V).quotientPositiveQuasitrace_metricSize_add
    (matrixStateUltralimitTriangle hsimple y hy f V) (matrixStateUltralimitSqrt hsimple y hy f V)

abbrev matrixStateAWPositive_sqrt :=
  (matrixStateUltralimitPositive hsimple y hy f V).quotientPositiveQuasitrace_sqrt_add
    (matrixStateUltralimitTriangle hsimple y hy f V) (matrixStateUltralimitSqrt hsimple y hy f V)

def matrixStateFinOneAW : FinMatrix A 1 →⋆ₐ[ℂ] NormalizedMatrixStateUltraAW hsimple y hy f V :=
  (matrixStateDiagonalAWEmbedding hsimple y hy f V).comp scalarFinOneEquiv.symm.toStarAlgHom

abbrev regularizedStateNormalization : ℝ≥0 :=
  ⟨(regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹,
    inv_nonneg.mpr ENNReal.toReal_nonneg⟩

include hsimple hy in
lemma regularizedStateNormalization_pos : 0 < regularizedStateNormalization y f :=
  inv_pos.mpr (ENNReal.toReal_pos (finiteState_regularized_unit hsimple y hy f).1.ne'
    (finiteState_regularized_unit hsimple y hy f).2)

lemma matrixStateFinOneAW_complex (M : FinMatrix A 1) :
    (matrixStateAWPositive hsimple y hy f V).complexValue
      (matrixStateFinOneAW hsimple y hy f V M) =
        (regularizedStateNormalization y f : ℂ)*
          (regularizedStateCauchyPositive hsimple y hy f).complexValue M := by
  rw [matrixStateAWPositive_complex]
  change matrixStateAWQuasitrace hsimple y hy f V
    (matrixStateDiagonalAWEmbedding hsimple y hy f V (scalarFinOneEquiv.symm M)) = _
  rw [matrixStateDiagonalAWEmbedding_value]
  rw [← normalizedMatrixStatePositiveQuasitrace_scalar_complex hsimple y hy f 0]
  change (normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0).complexValue
    (scalarFinOneEquiv (scalarFinOneEquiv.symm M)) = _
  rw [StarAlgEquiv.apply_symm_apply]
  change ((regularizedStateCauchyPositive hsimple y hy f).scale
    (⟨(matrixStateUnitValue hsimple y hy f 0)⁻¹,_⟩ : ℝ≥0)).complexValue M = _
  erw [PositiveQuasitrace.scale_complexValue]
  change (((matrixStateUnitValue hsimple y hy f 0)⁻¹ : ℝ) : ℂ)*
    (regularizedStateCauchyPositive hsimple y hy f).complexValue M = _
  rw [matrixStateUnitValue_zero]
  rfl

lemma matrixStateFinOneAW_positive (M : Positive (FinMatrix A 1)) :
    matrixStateAWPositive hsimple y hy f V
      (Positive.map (matrixStateFinOneAW hsimple y hy f V).toNonUnitalStarAlgHom M) =
        (regularizedStateNormalization y f : ℝ)*regularizedStateCauchyPositive hsimple y hy f M := by
  have h := matrixStateFinOneAW_complex hsimple y hy f V M.1
  have he : (matrixStateAWPositive hsimple y hy f V).complexValue
      (matrixStateFinOneAW hsimple y hy f V M.1) =
      ((matrixStateAWPositive hsimple y hy f V
        (Positive.map (matrixStateFinOneAW hsimple y hy f V).toNonUnitalStarAlgHom M) : ℝ) : ℂ) :=
    (matrixStateAWPositive hsimple y hy f V).complexValue_positive
      (Positive.map (matrixStateFinOneAW hsimple y hy f V).toNonUnitalStarAlgHom M)
  rw [he,(regularizedStateCauchyPositive hsimple y hy f).complexValue_positive M] at h
  exact_mod_cast h
end CuntzPureness

end

end OAI
