import OAI.Probability.FreeIsing.Posterior.DerivativeBounds
import OAI.Probability.FreeIsing.Posterior.SqrtObservationDerivative

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem367.FinitePosterior

variable {V : Type*} [Fintype V]

def gaussianObservationCurve (signal noise : V → ℝ) (t : ℝ) : V → ℝ :=
  t • signal + Real.sqrt t • noise

def gaussianObservationVelocity (signal noise : V → ℝ) (t : ℝ) : V → ℝ :=
  signal + (1 / (2 * Real.sqrt t)) • noise

theorem hasDerivAt_gaussianObservationCurve (signal noise : V → ℝ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianObservationCurve signal noise)
      (gaussianObservationVelocity signal noise t) t := by
  have hd := ((hasDerivAt_id t).smul_const signal).add
    ((Real.hasDerivAt_sqrt ht.ne').smul_const noise)
  change HasDerivAt (gaussianObservationCurve signal noise)
    (1 • signal + (1 / (2 * Real.sqrt t)) • noise) t at hd
  simpa only [gaussianObservationVelocity, one_smul] using hd

theorem hasDerivAt_along_gaussianObservationCurve
    (f : (V → ℝ) → ℝ) (g : (V → ℝ) → V → ℝ)
    (hdf : ∀ x, HasFDerivAt f (∑ v, g x v •
      (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x)
    (signal noise : V → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => f (gaussianObservationCurve signal noise r))
      (∑ v, g (gaussianObservationCurve signal noise t) v *
        gaussianObservationVelocity signal noise t v) t := by
  have hd := (hdf (gaussianObservationCurve signal noise t)).comp_hasDerivAt t
    (hasDerivAt_gaussianObservationCurve signal noise ht)
  simpa only [Function.comp_def, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul] using hd

omit [Fintype V] in
theorem gaussianObservationVelocity_bound (signal noise : V → ℝ)
    {t r : ℝ} (ht : 0 < t) (hr : t / 2 < r)
    (hsignal : ∀ v, |signal v| ≤ 1) (v : V) :
    |gaussianObservationVelocity signal noise r v| ≤
      1 + (1 / (2 * Real.sqrt (t / 2))) * |noise v| := by
  have hhalf : 0 < t / 2 := by positivity
  have hrpos : 0 < r := hhalf.trans hr
  have hsqrt : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.mpr hhalf
  have hcoef : 1 / (2 * Real.sqrt r) ≤ 1 / (2 * Real.sqrt (t / 2)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr.le) (by norm_num)
  change |signal v + (1 / (2 * Real.sqrt r)) * noise v| ≤ _
  calc
    _ ≤ |signal v| + |(1 / (2 * Real.sqrt r)) * noise v| := abs_add_le _ _
    _ = |signal v| + (1 / (2 * Real.sqrt r)) * |noise v| := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 / (2 * Real.sqrt r) by positivity)]
    _ ≤ _ := add_le_add (hsignal v)
      (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω]

theorem hasDerivAt_integral_gaussianObservationCurve
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : (V → ℝ) → ℝ) (g : (V → ℝ) → V → ℝ)
    (hdf : ∀ x, HasFDerivAt f (∑ v, g x v •
      (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x)
    (hg : ∀ v, Continuous (fun x => g x v))
    (M C : ℝ) (hC : 0 ≤ C)
    (hfbound : ∀ x, |f x| ≤ M) (hgbound : ∀ x v, |g x v| ≤ C)
    (signal noise : Ω → V → ℝ)
    (hsignal : Measurable signal) (hnoise : Measurable noise)
    (hspin : ∀ ω v, |signal ω v| ≤ 1)
    (hnoiseInt : ∀ v, Integrable (fun ω => noise ω v) μ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => ∫ ω, f (gaussianObservationCurve (signal ω) (noise ω) r) ∂μ)
      (∫ ω, ∑ v, g (gaussianObservationCurve (signal ω) (noise ω) t) v *
        gaussianObservationVelocity (signal ω) (noise ω) t v ∂μ) t := by
  let D : (V → ℝ) → (V → ℝ) →L[ℝ] ℝ := fun x => ∑ v, g x v •
    (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)
  have hDcont : Continuous D := by
    apply continuous_finsetSum
    intro v _
    exact (hg v).smul continuous_const
  have hDbound (x : V → ℝ) : ‖D x‖ ≤ (Fintype.card V : ℝ) * C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) hC)
    intro y
    simp only [D, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    calc
      ‖∑ v, g x v * y v‖ ≤ ∑ v, ‖g x v * y v‖ := norm_sum_le _ _
      _ ≤ ∑ v : V, C * ‖y‖ := by
        apply Finset.sum_le_sum
        intro v _
        rw [norm_mul, Real.norm_eq_abs (g x v)]
        exact mul_le_mul (hgbound x v) (norm_le_pi_norm y v) (norm_nonneg _) hC
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hsInt : Integrable signal μ := Integrable.of_eval fun v =>
    Integrable.of_bound ((measurable_pi_apply v).comp hsignal).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hspin ω v)
  have hnInt : Integrable noise μ :=
    ⟨hnoise.aestronglyMeasurable, (Integrable.of_eval hnoiseInt).hasFiniteIntegral⟩
  have hd := (hasDerivAt_integral_sqrt_observation_vector hsInt hnInt hdf hDcont
    hfbound (mul_nonneg (by positivity) hC) hDbound ht).2
  simpa only [gaussianObservationCurve, gaussianObservationVelocity, D, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using hd

end Expectation

section Posterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem continuous_fieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldCovariance energy spin observable x v) := by
  exact (continuous_fieldMean energy spin (fun s => observable s * spin s v)).sub
    ((continuous_fieldMean energy spin observable).mul
      (continuous_fieldMean energy spin (fun s => spin s v)))

theorem hasFDerivAt_fieldMean_square (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) :
    HasFDerivAt (fun y => fieldMean energy spin observable y ^ 2)
      (∑ v, (2 * fieldMean energy spin observable x * fieldCovariance energy spin observable x v) •
        (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x := by
  have hs : HasDerivAt (fun z : ℝ => z ^ 2)
      (2 * fieldMean energy spin observable x) (fieldMean energy spin observable x) := by
    have hd := (hasDerivAt_id (fieldMean energy spin observable x)).pow 2
    change HasDerivAt (fun z : ℝ => z ^ 2) _ (fieldMean energy spin observable x) at hd
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq] using hd
  have hd := hs.comp_hasFDerivAt x (hasFDerivAt_fieldMean energy spin observable x)
  simpa only [Function.comp_def, fieldMeanDerivative, Finset.smul_sum, smul_smul] using hd

variable {Ω : Type*} [MeasurableSpace Ω]

theorem hasDerivAt_integral_fieldMean_observation
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    (signal noise : Ω → V → ℝ)
    (hsignal : Measurable signal) (hnoise : Measurable noise)
    (hspin : ∀ ω v, |signal ω v| ≤ 1)
    (hnoiseInt : ∀ v, Integrable (fun ω => noise ω v) μ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => ∫ ω, fieldMean energy spin observable
        (gaussianObservationCurve (signal ω) (noise ω) r) ∂μ)
      (∫ ω, ∑ v, fieldCovariance energy spin observable
        (gaussianObservationCurve (signal ω) (noise ω) t) v *
          gaussianObservationVelocity (signal ω) (noise ω) t v ∂μ) t := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  exact hasDerivAt_integral_gaussianObservationCurve μ
    (fieldMean energy spin observable) (fieldCovariance energy spin observable)
    (hasFDerivAt_fieldMean energy spin observable)
    (continuous_fieldCovariance energy spin observable) A (2 * A) (by positivity)
    (fun x => abs_fieldMean_le energy spin observable x A hbound)
    (fun x v => abs_fieldCovariance_le energy spin observable x v A (fun s => hcoords s v) hbound)
    signal noise hsignal hnoise hspin hnoiseInt ht

theorem hasDerivAt_integral_fieldMean_square_observation
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (A : ℝ) (hbound : ∀ s, |observable s| ≤ A)
    (hcoords : ∀ s v, spin s v = -1 ∨ spin s v = 1)
    (signal noise : Ω → V → ℝ)
    (hsignal : Measurable signal) (hnoise : Measurable noise)
    (hspin : ∀ ω v, |signal ω v| ≤ 1)
    (hnoiseInt : ∀ v, Integrable (fun ω => noise ω v) μ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => ∫ ω, fieldMean energy spin observable
        (gaussianObservationCurve (signal ω) (noise ω) r) ^ 2 ∂μ)
      (∫ ω, ∑ v, (2 * fieldMean energy spin observable
        (gaussianObservationCurve (signal ω) (noise ω) t) *
        fieldCovariance energy spin observable (gaussianObservationCurve (signal ω) (noise ω) t) v) *
          gaussianObservationVelocity (signal ω) (noise ω) t v ∂μ) t := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  apply hasDerivAt_integral_gaussianObservationCurve μ
    (fun x => fieldMean energy spin observable x ^ 2)
    (fun x v => 2 * fieldMean energy spin observable x * fieldCovariance energy spin observable x v)
    (hasFDerivAt_fieldMean_square energy spin observable)
    (fun v => ((continuous_fieldMean energy spin observable).const_mul 2).mul
      (continuous_fieldCovariance energy spin observable v))
    (A ^ 2) (4 * A ^ 2) (by positivity)
    (fun x => abs_fieldMean_square_le energy spin observable x A hbound) ?_
    signal noise hsignal hnoise hspin hnoiseInt ht
  intro x v
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := abs_fieldMean_le energy spin observable x A hbound
  have hc := abs_fieldCovariance_le energy spin observable x v A (fun s => hcoords s v) hbound
  calc
    2 * |fieldMean energy spin observable x| * |fieldCovariance energy spin observable x v| ≤
      2 * A * (2 * A) := by gcongr
    _ = 4 * A ^ 2 := by ring

end Posterior

end Problem367.FinitePosterior

end

end OAI
