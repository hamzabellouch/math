import Mathlib
import OAI.Analysis.Conductivity.Fourier.AnalyticNull

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma analyticNull_euclidean (n : ℕ) : AnalyticNullProperty (EuclideanSpace ℝ (Fin n)) volume :=
  analyticNull_of_equiv volume volume
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))
    (PiLp.volume_preserving_ofLp (Fin n)) (analyticNull_fin n)

lemma analytic_directional_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U : Set E} (hf : AnalyticOnNhd ℝ f U) (w : E) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ f x w) U :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp_analyticOnNhd hf.fderiv

lemma analytic_gradient_minor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → ℝ} {U : Set E} (hu : AnalyticOnNhd ℝ u U)
    (hv : AnalyticOnNhd ℝ v U) (p q : E) :
    AnalyticOnNhd ℝ (fun x => fderiv ℝ u x p*fderiv ℝ v x q-
      fderiv ℝ u x q*fderiv ℝ v x p) U :=
  ((analytic_directional_fderiv hu p).mul (analytic_directional_fderiv hv q)).sub
    ((analytic_directional_fderiv hu q).mul (analytic_directional_fderiv hv p))

end ScalarConductivity

end

end OAI
