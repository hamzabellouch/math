import OAI.NumberTheory.TwoPoint.Halasz.HalaszFinitePhase
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! The moment interpolation used to absorb colliding long variables.
All functions live on the same finite coefficient torus. -/
namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_torus_geometric_mean {k : ℕ}
    (F G : (Fin k → AddCircle (1:ℝ)) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ x, 0≤F x) (hG0 : ∀ x, 0≤G x)
    {θ : ℝ} (hθ0 : 0<θ) (hθ1 : θ<1) :
    (∫ x, (F x)^θ*(G x)^(1-θ) ∂halaszVinogradovHaar k) ≤
      (∫ x, F x ∂halaszVinogradovHaar k)^θ *
        (∫ x, G x ∂halaszVinogradovHaar k)^(1-θ) := by
  have hq0 : 0<1-θ := by linarith
  have hFc : Continuous (fun x => (F x)^θ) :=
    hF.rpow_const (fun x => Or.inr hθ0.le)
  have hGc : Continuous (fun x => (G x)^(1-θ)) :=
    hG.rpow_const (fun x => Or.inr hq0.le)
  have hpq : (1/θ).HolderConjugate (1/(1-θ)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (one_lt_div hθ0).mpr hθ1
    · simp only [one_div,inv_inv]
      ring
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := halaszVinogradovHaar k) hpq
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hF0 x) _))
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hG0 x) _))
    (hFc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hGc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hp (x : Fin k → AddCircle (1:ℝ)) : ((F x)^θ)^(1/θ)=F x := by
    rw [← Real.rpow_mul (hF0 x),mul_one_div_cancel hθ0.ne',Real.rpow_one]
  have hq (x : Fin k → AddCircle (1:ℝ)) : ((G x)^(1-θ))^(1/(1-θ))=G x := by
    rw [← Real.rpow_mul (hG0 x),mul_one_div_cancel hq0.ne',Real.rpow_one]
  simp_rw [hp,hq] at h
  simpa only [one_div,inv_inv] using h

end TwoPointCorrelations

end OAI
