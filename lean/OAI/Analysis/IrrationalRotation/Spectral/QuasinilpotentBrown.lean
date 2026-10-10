import OAI.Analysis.IrrationalRotation.Operators.TracialLogNormSquare
import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentTraceDerivative
import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentDeterminantReduction
import OAI.Analysis.IrrationalRotation.Spectral.BrownDiracReduction

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra
namespace Invariant233
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

theorem re_trace_log_normalized_resolvent_eq_zero (τ : TracialState A) {a : A}
    (hQN : NormQuasinilpotent a) (hmom : ∀ n : ℕ, 0 < n → τ (a^n) = 0) (z : ℂ) :
    (τ (CFC.log (star (1-z • a) * (1-z • a)))).re = 0 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let b : ℝ → A := fun t => 1-t • (z • a)
  let F : ℝ → ℝ := fun t => (τ (CFC.log (star (b t) * b t))).re
  have hunit : ∀ t, IsUnit (b t) := by
    intro t
    simpa only [b, mul_smul, Complex.coe_smul] using
      hQN.isUnit_one_sub_smul ((t : ℂ)*z)
  have hb : ∀ t, HasDerivAt b (-(z • a)) t := by
    intro t
    simpa only [b, one_smul, id_eq] using
      ((hasDerivAt_id t).smul_const (z • a)).const_sub (1 : A)
  have hF : ∀ t, HasDerivAt F 0 t := by
    intro t
    have h := CFCLogSeries.hasDerivAt_re_trace_log_normSquare τ hunit hb
      (continuousAt_const : ContinuousAt (fun _ : ℝ => -(z • a)) t)
    have hz : τ (Ring.inverse (b t) * (-(z • a))) = 0 := by
      simpa only [b, mul_smul, Complex.coe_smul, neg_smul] using
        τ.inverse_one_sub_smul_mul_smul_eq_zero hQN hmom ((t : ℂ)*z) (-z)
    simpa only [F, hz, Complex.zero_re, mul_zero] using h
  have hconst := is_const_of_deriv_eq_zero
    (fun t => (hF t).differentiableAt) (fun t => (hF t).deriv) (1 : ℝ) 0
  simpa [F, b, CFC.log_one] using hconst

theorem fugledeKadisonDeterminant_normalized_resolvent_eq_one
    (τ : TracialState A) {a : A} (hQN : NormQuasinilpotent a)
    (hmom : ∀ n : ℕ, 0 < n → τ (a^n) = 0) (z : ℂ) :
    fugledeKadisonDeterminant τ (1-z • a) = 1 := by
  rw [fugledeKadisonDeterminant_one_sub_smul_of_normQuasinilpotent τ hQN,
    re_trace_log_normalized_resolvent_eq_zero τ hQN hmom]
  simp

theorem isBrownMeasure_dirac_zero_of_normQuasinilpotent_of_moments_zero
    (τ : TracialState A) {a : A} (hQN : NormQuasinilpotent a)
    (hmom : ∀ n : ℕ, 0 < n → τ (a^n) = 0)
    (hdet : fugledeKadisonDeterminant τ a = 0) :
    IsBrownMeasure τ a (Measure.dirac 0) := by
  apply (isBrownMeasure_dirac_zero_iff τ a).mpr
  exact ⟨hdet, fun z _ => fugledeKadisonDeterminant_normalized_resolvent_eq_one τ hQN hmom z⁻¹⟩

end Invariant233

end

end OAI
