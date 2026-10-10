import OAI.Probability.StrongRayleigh.LocalInnovation
import OAI.Probability.StrongRayleigh.InnovationCorrection
import OAI.Probability.StrongRayleigh.InnovationMean

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal

namespace Problem336AdditiveD139.WeightedLocalInnovation

variable {I : Type u_1} {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

def signal (S : Finset I) (θ : I → ℝ) (X : I → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i * X i ω

def drift (S : Finset I) (θ : I → ℝ) (b : I → Ω → ℝ → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i * b i ω t

def correction (S : Finset I) (θ : I → ℝ) (X : I → Ω → ℝ)
    (b : I → Ω → ℝ → ℝ) (u v : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i * InnovationCorrection.correction (X i ω) (b i ω) u v

theorem posterior_sum (S : Finset I) (θ : I → ℝ) {m : MeasurableSpace Ω}
    {X B : I → Ω → ℝ} (hX : ∀ i ∈ S, Integrable (X i) μ)
    (hB : ∀ i ∈ S, B i =ᵐ[μ] μ[X i | m]) :
    signal S θ B =ᵐ[μ] μ[signal S θ X | m] := by
  have hsum := condExp_finsetSum (μ := μ) (s := S)
    (f := fun i => θ i • X i) (fun i hi => (hX i hi).smul (θ i)) m
  have hscale : ∀ᵐ ω ∂μ, ∀ i ∈ S,
      μ[(θ i • X i) | m] ω = θ i * μ[X i | m] ω := by
    apply (S.eventually_all).mpr
    intro i hi
    filter_upwards [condExp_smul (μ := μ) (θ i) (X i) m] with ω hω
    exact hω
  have hf : (∑ i ∈ S, θ i • X i) = (fun ω => ∑ i ∈ S, θ i * X i ω) := by
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf] at hsum
  filter_upwards [hsum, hscale, (S.eventually_all).mpr hB] with ω hs hc hb
  simp only [Finset.sum_apply] at hs
  change (∑ i ∈ S, θ i * B i ω) = μ[(fun ω => ∑ i ∈ S, θ i * X i ω) | m] ω
  change μ[(fun ω => ∑ i ∈ S, θ i * X i ω) | m] ω =
    ∑ i ∈ S, μ[(θ i • X i) | m] ω at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i hi, hb i hi]

theorem correction_eq (S : Finset I) (θ : I → ℝ) (X : I → Ω → ℝ)
    (b : I → Ω → ℝ → ℝ) (u v : ℝ)
    (hb : ∀ i ∈ S, ∀ ω, IntervalIntegrable (b i ω) volume u v) (ω : Ω) :
    correction S θ X b u v ω =
      (v - u) * signal S θ X ω - ∫ t in u..v, drift S θ b t ω := by
  unfold correction signal drift InnovationCorrection.correction
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hb i hi ω).const_mul (θ i))]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem measurable_drift (S : Finset I) (θ : I → ℝ)
    {b : I → Ω → ℝ → ℝ}
    (hb : ∀ i ∈ S, Measurable (Function.uncurry (b i))) :
    Measurable (Function.uncurry (drift S θ b)) := by
  exact S.measurable_sum (fun i hi =>
    measurable_const.mul ((hb i hi).comp measurable_swap))

theorem abs_drift_le (S : Finset I) (θ : I → ℝ)
    {b : I → Ω → ℝ → ℝ}
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1) (t : ℝ) (ω : Ω) :
    |drift S θ b t ω| ≤ ∑ i ∈ S, |θ i| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_of_nonneg (hb i hi ω t).1]
  simpa using mul_le_mul_of_nonneg_left (hb i hi ω t).2 (abs_nonneg (θ i))

theorem intervalIntegrable_drift_coordinates (S : Finset I)
    {b : I → Ω → ℝ → ℝ}
    (hbm : ∀ i ∈ S, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1)
    (u v : ℝ) :
    ∀ i ∈ S, ∀ ω, IntervalIntegrable (b i ω) volume u v := by
  intro i hi ω
  exact InnovationCorrection.intervalIntegrable_of_measurable_unitInterval
    ((hbm i hi).comp (measurable_const.prodMk measurable_id)) (hb i hi ω) u v

theorem correction_condExp_zero [IsFiniteMeasure μ]
    (S : Finset I) (θ : I → ℝ) (H : Filtration ℝ mΩ)
    {X : I → Ω → ℝ} {b : I → Ω → ℝ → ℝ} {Q : Ω → ℝ} {u v : ℝ}
    (huv : u ≤ v)
    (hX : ∀ i ∈ S, Integrable (X i) μ)
    (hbm : ∀ i ∈ S, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1)
    (hQ : Integrable Q μ) (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    (hpost : ∀ t ∈ Ioc u v, ∀ i ∈ S,
      (fun ω => b i ω t) =ᵐ[μ] μ[X i | H t]) :
    μ[(fun ω => Q ω + correction S θ X b u v ω) | H u] =ᵐ[μ] 0 := by
  have hXi : Integrable (signal S θ X) μ :=
    integrable_finsetSum S (fun i hi => (hX i hi).const_mul (θ i))
  have hmean := InnovationMean.bounded_innovation_condExp_eq_zero H huv hXi hQ hQmean
    (measurable_drift S θ hbm) (abs_drift_le S θ hb) (fun t ht =>
      posterior_sum S θ hX (hpost t ht))
  have heq : (fun ω => Q ω + correction S θ X b u v ω) =
      (fun ω => (v - u) * signal S θ X ω + Q ω - ∫ t in u..v, drift S θ b t ω) := by
    funext ω
    rw [correction_eq S θ X b u v (intervalIntegrable_drift_coordinates S hbm hb u v)]
    ring
  rw [heq]
  exact hmean

def amplitude (S : Finset I) (θ : I → ℝ) : ℝ := ∑ i ∈ S, |θ i|

def variance (S : Finset I) (θ : I → ℝ) : ℝ≥0 :=
  ⟨∑ i ∈ S, θ i ^ 2, Finset.sum_nonneg (fun i _ => sq_nonneg (θ i))⟩

def errorConstant (S : Finset I) (θ : I → ℝ) : ℝ :=
  InnovationErrorScale.errorConstant (amplitude S θ) (Real.sqrt (variance S θ))
    GaussianMomentBounds.standardThirdAbsMoment

theorem amplitude_nonneg (S : Finset I) (θ : I → ℝ) : 0 ≤ amplitude S θ :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (θ i))

theorem errorConstant_nonneg (S : Finset I) (θ : I → ℝ) : 0 ≤ errorConstant S θ :=
  InnovationErrorScale.errorConstant_nonneg (amplitude_nonneg S θ) (Real.sqrt_nonneg _)
    GaussianMomentBounds.standardThirdAbsMoment_nonneg

theorem corrected_gaussian_characteristic_error [IsProbabilityMeasure μ]
    (S : Finset I) (θ : I → ℝ) (H : Filtration ℝ mΩ) (u : ℝ) (h : ℝ≥0)
    (h1 : (h : ℝ) ≤ 1) {mQ : MeasurableSpace Ω}
    {X : I → Ω → ℝ} {b : I → Ω → ℝ → ℝ} {Q : Ω → ℝ}
    (hxm : ∀ i ∈ S, Measurable[mΩ] (X i))
    (hx : ∀ i ∈ S, ∀ ω, X i ω ∈ Icc (0 : ℝ) 1)
    (hbm : ∀ i ∈ S, Measurable[mΩ.prod (borel ℝ)] (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1)
    (hleQ : mQ ≤ mΩ) (hmQ : StronglyMeasurable[mQ] Q)
    (hQ : HasLaw Q (gaussianReal 0 (h * variance S θ)) μ)
    (hind : Indep mQ (H u) μ)
    (hpost : ∀ t ∈ Ioc u (u + (h : ℝ)), ∀ i ∈ S,
      (fun ω => b i ω t) =ᵐ[μ] μ[X i | H t]) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I *
          ((Q a + correction S θ X b u (u + (h : ℝ)) a : ℝ) : ℂ)) | H u] ω -
          (Real.exp (-((h : ℝ) * (variance S θ : ℝ)) / 2) : ℂ)‖ ≤
        errorConstant S θ * (h : ℝ) * Real.sqrt h := by
  let : MeasurableSpace Ω := mΩ
  have huv : u ≤ u + (h : ℝ) := le_add_of_nonneg_right h.coe_nonneg
  have hXi : ∀ i ∈ S, Integrable (X i) μ := by
    intro i hi
    apply Integrable.of_bound (μ := μ) (hxm i hi).aestronglyMeasurable 1
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hx i hi ω).1] using (hx i hi ω).2
  have hQmean : μ[Q | H u] =ᵐ[μ] 0 :=
    (GaussianMomentBounds.conditional_gaussian_moments hQ hleQ (H.le u) hmQ hind).1
  have hmean := correction_condExp_zero S θ H huv hXi hbm hb
    (GaussianMomentBounds.integrable_of_hasLaw hQ) hQmean hpost
  have hRm : AEStronglyMeasurable[mΩ]
      (correction S θ X b u (u + (h : ℝ))) μ :=
    (InnovationCorrection.measurable_sum_correction S θ hxm hbm u (u + (h : ℝ))).aestronglyMeasurable
  have hR : ∀ᵐ ω ∂μ, |correction S θ X b u (u + (h : ℝ)) ω| ≤ amplitude S θ * (h : ℝ) := by
    filter_upwards with ω
    have hbound := InnovationCorrection.abs_sum_correction_le S θ
      (fun i => X i ω) (fun i => b i ω) huv
      (fun i hi => hx i hi ω) (fun i hi t _ => hb i hi ω t)
    simpa only [correction, amplitude, add_sub_cancel_left, mul_comm] using hbound
  exact LocalInnovation.gaussian_perturbation_characteristic_error hleQ (H.le u)
    hQ hmQ hind hRm (amplitude_nonneg S θ) h1 hR hmean

def noiseIncrement (S : Finset I) (θ : I → ℝ) (B : I → Ω → ℝ → ℝ)
    (u v : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i * (B i ω v - B i ω u)

def innovationIncrement (S : Finset I) (θ : I → ℝ) (X : I → Ω → ℝ)
    (B b : I → Ω → ℝ → ℝ) (u v : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ S, θ i *
    (InnovationCorrection.innovation (X i ω) (B i ω) (b i ω) v -
      InnovationCorrection.innovation (X i ω) (B i ω) (b i ω) u)

theorem innovationIncrement_eq (S : Finset I) (θ : I → ℝ)
    (X : I → Ω → ℝ) (B b : I → Ω → ℝ → ℝ) (u v : ℝ)
    (hbm : ∀ i ∈ S, Measurable (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1) :
    innovationIncrement S θ X B b u v =
      fun ω => noiseIncrement S θ B u v ω + correction S θ X b u v ω := by
  funext ω
  exact InnovationCorrection.sum_innovation_sub_eq S θ (fun i => X i ω)
    (fun i => B i ω) (fun i => b i ω)
    (fun i hi => intervalIntegrable_drift_coordinates S hbm hb 0 u i hi ω)
    (fun i hi => intervalIntegrable_drift_coordinates S hbm hb u v i hi ω)

theorem innovation_characteristic_error [IsProbabilityMeasure μ]
    (S : Finset I) (θ : I → ℝ) (H : Filtration ℝ mΩ) (u : ℝ) (h : ℝ≥0)
    (h1 : (h : ℝ) ≤ 1) {mQ : MeasurableSpace Ω}
    {X : I → Ω → ℝ} {B b : I → Ω → ℝ → ℝ}
    (hxm : ∀ i ∈ S, Measurable[mΩ] (X i))
    (hx : ∀ i ∈ S, ∀ ω, X i ω ∈ Icc (0 : ℝ) 1)
    (hbm : ∀ i ∈ S, Measurable[mΩ.prod (borel ℝ)] (Function.uncurry (b i)))
    (hb : ∀ i ∈ S, ∀ ω t, b i ω t ∈ Icc (0 : ℝ) 1)
    (hleQ : mQ ≤ mΩ)
    (hmQ : StronglyMeasurable[mQ] (noiseIncrement S θ B u (u + (h : ℝ))))
    (hQ : HasLaw (noiseIncrement S θ B u (u + (h : ℝ)))
      (gaussianReal 0 (h * variance S θ)) μ)
    (hind : Indep mQ (H u) μ)
    (hpost : ∀ t ∈ Ioc u (u + (h : ℝ)), ∀ i ∈ S,
      (fun ω => b i ω t) =ᵐ[μ] μ[X i | H t]) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I *
          (innovationIncrement S θ X B b u (u + (h : ℝ)) a : ℂ)) | H u] ω -
          (Real.exp (-((h : ℝ) * (variance S θ : ℝ)) / 2) : ℂ)‖ ≤
        errorConstant S θ * (h : ℝ) * Real.sqrt h := by
  let : MeasurableSpace Ω := mΩ
  rw [innovationIncrement_eq S θ X B b u (u + (h : ℝ)) hbm hb]
  exact corrected_gaussian_characteristic_error S θ H u h h1
    hxm hx hbm hb hleQ hmQ hQ hind hpost

end Problem336AdditiveD139.WeightedLocalInnovation

end

end OAI
