import OAI.Analysis.OperatorAlgebra.SmallTimeOperatorAverage
import OAI.Analysis.ModularTheory.RightContinuity
import OAI.Analysis.ModularTheory.CoreDualAction
import OAI.Analysis.ModularTheory.FourierTranslation

namespace OAI

/-! Contractive Gaussian regularization by the concrete dual action,
converging strongly to the original operator. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularDual_continuous (f : Lp H 2 (volume : Measure ℝ)) :
    Continuous (fun r => modularDual volume r f) := by
  have he (r : ℝ) : modularDual volume r f =
      𝓕 (modularLpTranslate volume (r / (-2 * Real.pi)) (𝓕⁻ f)) := by
    rw [fourier_modularLpTranslate, fourier_fourierInv_eq]
    congr 1
    field_simp [Real.pi_ne_zero]
  have hc := (Lp.fourierTransformₗᵢ ℝ H).continuous.comp
    ((continuous_modularLpTranslate (𝓕⁻ f)).comp (continuous_id.div_const (-2 * Real.pi)))
  exact hc.congr (fun r => (he r).symm)

def modularDualOperator (r : ℝ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  (modularDualUnitary volume r).toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace H] in
lemma modularDual_operator_norm_le (r : ℝ) :
    ‖modularDualOperator (H := H) r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖modularDual volume r f‖ ≤ 1 * ‖f‖
  rw [modularDual_norm, one_mul]

lemma modularDualConjugation_continuous
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f : Lp H 2 (volume : Measure ℝ)) :
    Continuous (fun r => modularDualConjugation volume r T f) := by
  have hi : Continuous (fun r => T (modularDual volume (-r) f)) :=
    T.continuous.comp ((modularDual_continuous f).comp continuous_neg)
  have ho : ∀ x : Lp H 2 (volume : Measure ℝ),
      Continuous (fun r => modularDualOperator r x) := modularDual_continuous
  change Continuous (fun r => modularDualOperator r (T (modularDual volume (-r) f)))
  exact continuous_operator_apply_varying (modularDualOperator (H := H))
    modularDual_operator_norm_le ho _ hi

lemma modularDualConjugation_norm_le
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) (r : ℝ) :
    ‖modularDualConjugation volume r T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  change ‖modularDualUnitary volume r (T (modularDualUnitary volume (-r) f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using T.le_opNorm (modularDualUnitary volume (-r) f)

def modularDualGaussianAverage
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) (n : ℕ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  smallTimeOperatorAverage (fun r => modularDualConjugation volume r T)
    (modularDualConjugation_continuous T) ‖T‖ (modularDualConjugation_norm_le T) n

lemma modularDualGaussianAverage_norm_le
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) (n : ℕ) :
    ‖modularDualGaussianAverage T n‖ ≤ ‖T‖ :=
  smallTimeOperatorAverage_norm_le _ _ _ _ n

lemma modularDualGaussianAverage_strong
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => modularDualGaussianAverage T n f) atTop (𝓝 (T f)) := by
  have h := smallTimeOperatorAverage_strong (fun r => modularDualConjugation volume r T)
    (modularDualConjugation_continuous T) ‖T‖ (modularDualConjugation_norm_le T) f
  simpa only [modularDualGaussianAverage, modularDualConjugation_zero] using h

lemma modularDualGaussianAverage_mem (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct volume S) (n : ℕ) :
    modularDualGaussianAverage T n ∈ modularCrossedProduct volume S := by
  rw [← (modularCrossedProduct volume S).commutant_commutant,
    VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  apply ContinuousLinearMap.ext
  intro f
  have hi := BoundedRecovery.integrable_smul_bounded_orbit
    realGaussianDensity_integrable.ofReal
    ((modularDualConjugation_continuous T f).comp (continuous_id.div_const (n + 1 : ℝ)))
    (fun r => ((modularDualConjugation volume (r / (n + 1 : ℝ)) T).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (modularDualConjugation_norm_le T _) (norm_nonneg f)))
  change Integrable (fun r : ℝ => (realGaussianDensity r : ℂ) •
    modularDualConjugation volume (r / (n + 1 : ℝ)) T f) at hi
  change b (∫ r, (realGaussianDensity r : ℂ) •
      modularDualConjugation volume (r / (n + 1 : ℝ)) T f) =
    ∫ r, (realGaussianDensity r : ℂ) •
      modularDualConjugation volume (r / (n + 1 : ℝ)) T (b f)
  rw [← b.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [map_smul]
  congr 1
  exact (congrArg
    (fun R : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) => R f)
    (VonNeumannAlgebra.mem_commutant_iff.mp hb _
      (modularDualConjugation_mem volume S _ hT))).symm

end WeakPureInfiniteness

end

end OAI
