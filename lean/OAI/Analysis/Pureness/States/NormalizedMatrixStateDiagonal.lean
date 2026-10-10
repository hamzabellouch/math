import OAI.Analysis.Pureness.States.NormalizedMatrixStateUltraproduct
import OAI.Analysis.Pureness.Quasitrace.QuasitraceMatrixDiagonal

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

lemma matrixStateUnitValue_zero :
    matrixStateUnitValue hsimple y hy f 0 =
      (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal := by
  change (finiteSpectralIntegral (regularizedFiniteDimension f.toAddHom f.monotone) 1 ⟨1,zero_le_one⟩).toReal = _
  rw [finiteSpectralIntegral_projection _ _ _ (by simp [IsIdempotentElem])]
  rfl

lemma matrixStateUnitValue_eq (n : ℕ) :
    matrixStateUnitValue hsimple y hy f n = (n+1 : ℝ)*matrixStateUnitValue hsimple y hy f 0 := by
  have h := finiteSpectralPositiveQuasitrace_scalarMatrix
    (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f) n ⟨1,zero_le_one⟩
  have he (m : ℕ) : Positive.map (scalarMatrixHom (ι := Fin m)).toNonUnitalStarAlgHom
      (⟨1,zero_le_one⟩ : Positive A) = ⟨1,zero_le_one⟩ := Subtype.ext (map_one scalarMatrixHom)
  simp only [he] at h
  exact h

variable [Nontrivial A]

lemma normalizedMatrixStatePositiveQuasitrace_scalar (n : ℕ) (a : Positive A) :
    normalizedMatrixStatePositiveQuasitrace hsimple y hy f n
      (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) =
        normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0
          (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) := by
  change (matrixStateUnitValue hsimple y hy f n)⁻¹*
    finiteSpectralPositiveQuasitrace _ _ _ _ (n+1) (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) =
      (matrixStateUnitValue hsimple y hy f 0)⁻¹*
        finiteSpectralPositiveQuasitrace _ _ _ _ 1 (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a)
  rw [matrixStateUnitValue_eq,finiteSpectralPositiveQuasitrace_scalarMatrix]
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp

lemma normalizedMatrixStatePositiveQuasitrace_scalar_complex (n : ℕ) (x : A) :
    (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n).complexValue
      (scalarMatrixHom (ι := Fin (n+1)) x) =
        (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base x := by
  let P := (normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0).comap
    (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom
  have h := PositiveQuasitrace.complexValue_map
    (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n) P
    (scalarMatrixHom (A := A) (ι := Fin (n+1))).toNonUnitalStarAlgHom
    (normalizedMatrixStatePositiveQuasitrace_scalar hsimple y hy f n) x
  calc
    _ = P.complexValue x := h
    _ = _ := by
      change ((normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0).comap _).complexValue x = _
      rw [PositiveQuasitrace.comap_complexValue]
      change ((finiteSpectralPositiveQuasitrace _ _ _ _ 1).scale
        ⟨(matrixStateUnitValue hsimple y hy f 0)⁻¹,_⟩).complexValue
          (scalarMatrixHom (ι := Fin 1) x) = _
      refine (PositiveQuasitrace.scale_complexValue _ _ _).trans ?_
      change (((matrixStateUnitValue hsimple y hy f 0)⁻¹ : ℝ) : ℂ)*
        (finiteSpectralPositiveQuasitrace _ _ _ _ 1).complexValue (scalarMatrixHom (ι := Fin 1) x) = _
      rw [matrixStateUnitValue_zero]
      change _ = (((regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹ : ℝ) : ℂ)*
        ((finiteSpectralPositiveQuasitrace _ _ _ _ 1).comap
          (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom).complexValue x
      rw [PositiveQuasitrace.comap_complexValue]
      rfl

def matrixStateDiagonalProduct : A →⋆ₐ[ℂ] lp (fun n : ℕ => FinMatrix A (n+1)) ∞ where
  toFun x := ⟨fun n => scalarMatrixHom (ι := Fin (n+1)) x,
    memℓp_infty ⟨‖x‖,by
      rintro _ ⟨n,rfl⟩
      exact NonUnitalStarAlgHom.norm_apply_le (scalarMatrixHom (A := A) (ι := Fin (n+1))).toNonUnitalStarAlgHom x⟩⟩
  map_zero' := by apply lp.ext; funext n; exact map_zero (scalarMatrixHom (A := A) (ι := Fin (n+1)))
  map_one' := by apply lp.ext; funext n; exact map_one (scalarMatrixHom (A := A) (ι := Fin (n+1)))
  map_add' x y := by apply lp.ext; funext n; exact map_add (scalarMatrixHom (A := A) (ι := Fin (n+1))) x y
  map_mul' x y := by apply lp.ext; funext n; exact map_mul (scalarMatrixHom (A := A) (ι := Fin (n+1))) x y
  commutes' c := by apply lp.ext; funext n; exact (scalarMatrixHom (A := A) (ι := Fin (n+1))).commutes c
  map_star' x := by apply lp.ext; funext n; exact map_star (scalarMatrixHom (A := A) (ι := Fin (n+1))) x

variable (U : Ultrafilter ℕ)

lemma matrixStateUltraPositive_diagonal (a : Positive A) :
    ultralimitPositiveQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
      (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
      (Positive.map (matrixStateDiagonalProduct (A := A)).toNonUnitalStarAlgHom a) =
        normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0
          (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) := by
  apply tendsto_nhds_unique (quasitraceUltraPositive_tendsto
    (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (Positive.map (matrixStateDiagonalProduct (A := A)).toNonUnitalStarAlgHom a))
  have he (n : ℕ) : normalizedMatrixStatePositiveQuasitrace hsimple y hy f n
      (boundedProductPositiveEval n (Positive.map (matrixStateDiagonalProduct (A := A)).toNonUnitalStarAlgHom a)) =
        normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0
          (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) :=
    normalizedMatrixStatePositiveQuasitrace_scalar hsimple y hy f n a
  simp only [he]
  exact tendsto_const_nhds

def matrixStateDiagonalAWEmbedding : A →⋆ₐ[ℂ] NormalizedMatrixStateUltraAW hsimple y hy f U :=
  (ultralimitCompletionMap (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)).comp matrixStateDiagonalProduct

lemma matrixStateDiagonalAWEmbedding_value (x : A) :
    ultralimitAWQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
      (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
      (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
      (matrixStateDiagonalAWEmbedding hsimple y hy f U x) =
        (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base x := by
  dsimp only [matrixStateDiagonalAWEmbedding, StarAlgHom.comp_apply]
  rw [ultralimitAWQuasitrace_original]
  let P := (normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0).comap
    (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom
  have h := PositiveQuasitrace.complexValue_map
    (ultralimitPositiveQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
      (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)) P
    (matrixStateDiagonalProduct (A := A)).toNonUnitalStarAlgHom
    (matrixStateUltraPositive_diagonal hsimple y hy f U) x
  calc
    _ = P.complexValue x := h
    _ = _ := by
      rw [PositiveQuasitrace.comap_complexValue]
      exact normalizedMatrixStatePositiveQuasitrace_scalar_complex hsimple y hy f 0 x
end CuntzPureness

end

end OAI
