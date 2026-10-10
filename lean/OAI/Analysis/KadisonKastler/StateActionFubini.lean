import OAI.Analysis.KadisonKastler.StateActionAverages
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Commutation of probability averages of an abelian action -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem stateActionOrbit_average_apply (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) (s : ℝ) (x : H) :
    stateActionOrbit U (stateActionAverage U hU μ a) s x =
      ∫ t, stateActionOrbit U a (s+t) x ∂μ := by
  let u := U (Multiplicative.ofAdd s)
  have hi := integrable_bounded_operator_vector μ (stateActionOrbit U a)
    (fun y => (stateActionOrbit_continuous U hU a y).aestronglyMeasurable)
    (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)
    (star (u : H →L[ℂ] H) x)
  change (u : H →L[ℂ] H) (∫ t, stateActionOrbit U a t (star (u : H →L[ℂ] H) x) ∂μ)=_
  rw [← (u : H →L[ℂ] H).integral_comp_comm hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  change (u : H →L[ℂ] H) (stateActionOrbit U a t (star (u : H →L[ℂ] H) x)) =
    stateActionOrbit U a (s+t) x
  rw [stateActionOrbit_add]
  rfl

theorem stateActionAverage_commute (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a : H →L[ℂ] H) :
    stateActionAverage U hU μ (stateActionAverage U hU ν a) =
      stateActionAverage U hU ν (stateActionAverage U hU μ a) := by
  ext x
  change (∫ s, stateActionOrbit U (stateActionAverage U hU ν a) s x ∂μ)=
    ∫ t, stateActionOrbit U (stateActionAverage U hU μ a) t x ∂ν
  simp_rw [stateActionOrbit_average_apply]
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => stateActionOrbit U a (p.1+p.2) x) (μ.prod ν) :=
    ((stateActionOrbit_continuous U hU a x).comp
      (continuous_fst.add continuous_snd)).aestronglyMeasurable
  have hi : Integrable (fun p : ℝ × ℝ => stateActionOrbit U a (p.1+p.2) x)
      (μ.prod ν) := by
    apply (integrable_const (‖a‖*‖x‖)).mono' hm
    apply Eventually.of_forall
    intro p
    exact ((stateActionOrbit U a (p.1+p.2)).le_opNorm x).trans_eq
      (by rw [stateActionOrbit_norm])
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  change stateActionOrbit U a (s+t) x=stateActionOrbit U a (t+s) x
  rw [add_comm s t]

theorem invariant_functional_actionAverage
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hφ : ∀ t a, φ (stateActionOrbit U a t)=φ a)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) (ha : Continuous (stateActionOrbit U a)) :
    φ (stateActionAverage U hU μ a)=φ a := by
  have hi : Integrable (stateActionOrbit U a) μ := by
    apply (integrable_const ‖a‖).mono' ha.aestronglyMeasurable
    exact Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le
  have he : stateActionAverage U hU μ a=∫ t, stateActionOrbit U a t ∂μ := by
    ext x
    exact (ContinuousLinearMap.apply ℂ H x).integral_comp_comm hi
  rw [he,← φ.integral_comp_comm hi]
  simp_rw [hφ]
  simp only [integral_const,probReal_univ,one_smul]

end

end KadisonKastler

end OAI
