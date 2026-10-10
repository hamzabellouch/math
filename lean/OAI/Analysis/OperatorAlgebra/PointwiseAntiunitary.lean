import OAI.Analysis.ModularTheory.LpRepresentation
import OAI.Analysis.OperatorAlgebra.AntiunitaryCPConjugation

namespace OAI

/-! Pointwise antiunitary conjugation on the actual vector-valued L² space. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure ℝ)

def pointwiseAntiunitaryMap (J : H ≃ₗᵢ⋆[ℂ] H) : Lp H 2 μ →L⋆[ℂ] Lp H 2 μ :=
  J.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ

lemma pointwiseAntiunitaryMap_ae (J : H ≃ₗᵢ⋆[ℂ] H) (f : Lp H 2 μ) :
    pointwiseAntiunitaryMap μ J f =ᵐ[μ] fun t => J (f t) :=
  J.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f

lemma pointwiseAntiunitaryMap_norm (J : H ≃ₗᵢ⋆[ℂ] H) (f : Lp H 2 μ) :
    ‖pointwiseAntiunitaryMap μ J f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [pointwiseAntiunitaryMap_ae μ J f] with t ht
  rw [ht, J.norm_map]

lemma pointwiseAntiunitaryMap_inverse (J : H ≃ₗᵢ⋆[ℂ] H) (f : Lp H 2 μ) :
    pointwiseAntiunitaryMap μ J.symm (pointwiseAntiunitaryMap μ J f) = f := by
  apply Lp.ext
  filter_upwards [pointwiseAntiunitaryMap_ae μ J.symm (pointwiseAntiunitaryMap μ J f),
    pointwiseAntiunitaryMap_ae μ J f] with t h₁ h₂
  rw [h₁, h₂, J.symm_apply_apply]

def pointwiseAntiunitary (J : H ≃ₗᵢ⋆[ℂ] H) : Lp H 2 μ ≃ₗᵢ⋆[ℂ] Lp H 2 μ where
  toFun := pointwiseAntiunitaryMap μ J
  invFun := pointwiseAntiunitaryMap μ J.symm
  left_inv := pointwiseAntiunitaryMap_inverse μ J
  right_inv := pointwiseAntiunitaryMap_inverse μ J.symm
  map_add' := map_add (pointwiseAntiunitaryMap μ J)
  map_smul' c f := (pointwiseAntiunitaryMap μ J).map_smulₛₗ c f
  norm_map' := pointwiseAntiunitaryMap_norm μ J

lemma pointwiseAntiunitary_involutive (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) :
    Function.Involutive (pointwiseAntiunitary μ J) := by
  intro f
  apply Lp.ext
  filter_upwards [pointwiseAntiunitaryMap_ae μ J (pointwiseAntiunitaryMap μ J f),
    pointwiseAntiunitaryMap_ae μ J f] with t h₁ h₂
  change (pointwiseAntiunitaryMap μ J (pointwiseAntiunitaryMap μ J f)) t = _
  rw [h₁, h₂, hJ]

variable [CompleteSpace H]

lemma pointwiseAntiunitary_conjugate (J : H ≃ₗᵢ⋆[ℂ] H) (T : H →L[ℂ] H) :
    antiunitaryConjugate (pointwiseAntiunitary μ J) (pointwiseLpRepresentation μ T) =
      pointwiseLpRepresentation μ (antiunitaryConjugate J T) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [pointwiseAntiunitaryMap_ae μ J
      (pointwiseLpRepresentation μ T (pointwiseAntiunitaryMap μ J f)),
    T.coeFn_compLpL (p := 2) (μ := μ) (pointwiseAntiunitaryMap μ J f),
    pointwiseAntiunitaryMap_ae μ J f,
    (antiunitaryConjugate J T).coeFn_compLpL (p := 2) (μ := μ) f] with t h₁ h₂ h₃ h₄
  change (pointwiseAntiunitaryMap μ J
    (pointwiseLpRepresentation μ T (pointwiseAntiunitaryMap μ J f))) t =
    ((antiunitaryConjugate J T).compLpL 2 μ f) t
  change (pointwiseLpRepresentation μ T (pointwiseAntiunitaryMap μ J f)) t =
    T ((pointwiseAntiunitaryMap μ J f) t) at h₂
  rw [h₁, h₂, h₃, h₄]
  rfl

end WeakPureInfiniteness

end

end OAI
