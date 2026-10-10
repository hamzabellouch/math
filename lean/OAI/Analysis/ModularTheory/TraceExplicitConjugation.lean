import OAI.Analysis.ModularTheory.NormalWeightTotality
import OAI.Analysis.ModularTheory.TraceNormalConjugation

namespace OAI

/-! The tracial conjugation is the explicit Fourier-gauge conjugation on the
whole modular Hilbert space, by normal-weight totality. -/
noncomputable section
open MeasureTheory FourierTransform
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularWeightAdjointSemilinear (S : StandardModularData H) :
    Lp H 2 (volume : Measure ℝ) →SL[starRingEnd ℂ] Lp H 2 (volume : Measure ℝ) :=
  (Lp.fourierTransformₗᵢ ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((modularConjugationLp S).comp
      ((Lp.fourierTransformₗᵢ ℝ H).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (S.D.lpGaugeEquiv volume 1).toContinuousLinearEquiv.toContinuousLinearMap))

lemma modularWeightAdjointSemilinear_apply (S : StandardModularData H)
    (f : Lp H 2 (volume : Measure ℝ)) :
    modularWeightAdjointSemilinear S f = modularWeightAdjointMap S f := rfl

lemma modularTraceConjugation_eq_explicit (S : StandardModularData H)
    (f : Lp H 2 (volume : Measure ℝ)) :
    modularTraceConjugation S f = modularWeightAdjointMap S f := by
  have h : (modularTraceConjugation S).toContinuousLinearMap -
      modularWeightAdjointSemilinear S = 0 := by
    apply modularNormalWeight_annihilator_eq_zero S
    intro a ha g hg
    change modularTraceConjugation S _ - modularWeightAdjointMap S _ = 0
    exact sub_eq_zero.mpr (modularTraceConjugation_normal S a ha g hg)
  have he := congrArg
    (fun T : Lp H 2 (volume : Measure ℝ) →SL[starRingEnd ℂ]
      Lp H 2 (volume : Measure ℝ) => T f) h
  exact sub_eq_zero.mp he

end WeakPureInfiniteness

end

end OAI
