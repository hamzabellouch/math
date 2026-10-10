import OAI.Analysis.ModularTheory.TraceExplicitConjugation

namespace OAI

/-! On the original coefficient algebra, the core's tracial right action is
the pointwise original standard-form right action. -/
noncomputable section
open MeasureTheory FourierTransform
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularGauge_coefficient (S : StandardModularData H) (a : H →L[ℂ] H)
    (f : Lp H 2 (volume : Measure ℝ)) :
    S.D.lpGauge volume 1 (modularLpRepresentation volume S.D a f) =
      a.compLpL 2 volume (S.D.lpGauge volume 1 f) := by
  apply Lp.ext
  filter_upwards [S.D.lpGauge_ae volume 1 (modularLpRepresentation volume S.D a f),
    modularLpRepresentation_ae volume S.D a f,
    a.coeFn_compLpL (S.D.lpGauge volume 1 f), S.D.lpGauge_ae volume 1 f]
    with t hU hA hC hF
  rw [hU, one_mul, hA, hC, hF, one_mul, ← mul_apply_eq_comp,
    S.D.unitary_mul_neg, one_apply_eq_self]

lemma modularConjugationLp_coefficient (S : StandardModularData H) (a : H →L[ℂ] H)
    (f : Lp H 2 (volume : Measure ℝ)) :
    modularConjugationLp S (a.compLpL 2 volume f) =
      (antiunitaryConjugate S.J a).compLpL 2 volume (modularConjugationLp S f) := by
  apply Lp.ext
  filter_upwards [modularConjugationLp_ae S (a.compLpL 2 volume f),
    a.coeFn_compLpL f,
    (antiunitaryConjugate S.J a).coeFn_compLpL (modularConjugationLp S f),
    modularConjugationLp_ae S f] with t hJ hA hC hF
  rw [hJ, hA, hC, hF, antiunitaryConjugate_apply, S.conjugation (f t)]

lemma modularWeightAdjointMap_coefficient (S : StandardModularData H)
    (a : H →L[ℂ] H) (f : Lp H 2 (volume : Measure ℝ)) :
    modularWeightAdjointMap S (modularLpRepresentation volume S.D a f) =
      (antiunitaryConjugate S.J a).compLpL 2 volume (modularWeightAdjointMap S f) := by
  unfold modularWeightAdjointMap
  rw [modularGauge_coefficient, fourier_compLp,
    modularConjugationLp_coefficient, fourierInv_compLp]

lemma modularTracialRightAction_coefficient (S : StandardModularData H)
    (a : H →L[ℂ] H) :
    modularTracialRightAction S (modularLpRepresentation volume S.D a) =
      pointwiseLpRepresentation volume (antiunitaryConjugate S.J (star a)) := by
  apply ContinuousLinearMap.ext
  intro f
  change modularTraceConjugation S
    (star (modularLpRepresentation volume S.D a) (modularTraceConjugation S f)) = _
  rw [← map_star, modularTraceConjugation_eq_explicit,
    modularWeightAdjointMap_coefficient,
    ← modularTraceConjugation_eq_explicit,
    modularTraceConjugation_involutive]
  rfl

end WeakPureInfiniteness

end

end OAI
