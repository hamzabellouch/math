import OAI.Probability.SpanningForest.InnovationErrorRate
import OAI.Probability.SpanningForest.InnovationPhaseRecurrence
import OAI.Probability.SpanningForest.InnovationLawIdentification

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem336.InnovationGaussianProcess

theorem restricted_characteristic_of_gaussian_perturbations
    {Ω T : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (X : T → Ω → ℝ) (s t : T) (τ : ℕ → ℕ → T)
    (past : ℕ → ℕ → MeasurableSpace Ω)
    (hpast : ∀ n k, past n k ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet A)
    (hApast : ∀ n k, MeasurableSet[past n k] A)
    (hXstart : ∀ n k, Measurable[past n k] (X s))
    (hXpast : ∀ n k, Measurable[past n k] (X (τ n k)))
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (duration c L : ℝ) (hduration : 0 ≤ duration) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (Q R : ℕ → ℕ → Ω → ℝ) (variance : ℕ → ℕ → ℝ≥0)
    (hLaw : ∀ n k, k < n + 1 → HasLaw (Q n k) (gaussianReal 0 (variance n k)) P)
    (hvariance : ∀ n k, k < n + 1 →
      (variance n k : ℝ) = (duration / ((n + 1 : ℕ) : ℝ)) * c)
    (hR : ∀ n k, k < n + 1 → AEStronglyMeasurable (R n k) P)
    (hRbound : ∀ n k, k < n + 1 → ∀ᵐ ω ∂P,
      |R n k ω| ≤ (duration / ((n + 1 : ℕ) : ℝ)) * L)
    (hdecomp : ∀ n k, k < n + 1 → ∀ᵐ ω ∂P,
      X (τ n (k + 1)) ω - X (τ n k) ω = Q n k ω + R n k ω)
    (hIndep : ∀ n k, k < n + 1 → ∀ K : Ω → ℂ,
      Measurable[past n k] K → IndepFun K (Q n k) P)
    (hmean : ∀ n k, k < n + 1 → ∀ K : Ω → ℂ,
      Measurable[past n k] K → (∀ ω, ‖K ω‖ ≤ 1) →
      (∫ ω, K ω * ((X (τ n (k + 1)) ω - X (τ n k) ω : ℝ) : ℂ) ∂P) = 0) :
    (∫ ω in A, Complex.exp (((X t ω - X s ω : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-duration * (c / 2)) : ℂ) * (P.real A : ℂ) := by
  apply InnovationPhaseRecurrence.restricted_characteristic_of_bounded_test_steps
    X s t τ past hA hApast hXstart hXpast hstart hfinish
    (Innovation.gaussianErrorConstant L c) duration (c / 2) hduration (by positivity)
  have hquot : Tendsto (fun n : ℕ => duration / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat duration).comp (tendsto_add_atTop_nat 1)
  have htimes : Tendsto (fun n : ℕ => (duration / ((n + 1 : ℕ) : ℝ)) * c)
      atTop (𝓝 0) := by simpa using hquot.mul_const c
  have hsmall1 : ∀ᶠ n : ℕ in atTop, duration / ((n + 1 : ℕ) : ℝ) < 1 :=
    hquot.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hsmall2 : ∀ᶠ n : ℕ in atTop,
      (duration / ((n + 1 : ℕ) : ℝ)) * c < 2 :=
    htimes.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [hsmall1, hsmall2] with n hn1 hn2
  intro k hk K hKmeas hKbound
  have hKΩ : Measurable K := hKmeas.mono (hpast n k) le_rfl
  have hmean' : (∫ ω, K ω * ((Q n k ω + R n k ω : ℝ) : ℂ) ∂P) = 0 := by
    rw [← hmean n k hk K hKmeas hKbound]
    apply integral_congr_ae
    filter_upwards [hdecomp n k hk] with ω hω
    rw [hω]
  have hstep := Innovation.gaussian_smallStep_characteristic
    (hLaw n k hk) (hIndep n k hk K hKmeas) (hR n k hk)
    (div_nonneg hduration (by positivity)) hn1.le hL
    (hvariance n k hk) hn2.le (hRbound n k hk) hKΩ.aestronglyMeasurable
    (Filter.Eventually.of_forall hKbound) hmean'
  have hphase : (∫ ω, K ω * Complex.exp (((Q n k ω + R n k ω : ℝ) : ℂ) * Complex.I) ∂P) =
      ∫ ω, K ω * Complex.exp (((X (τ n (k + 1)) ω - X (τ n k) ω : ℝ) : ℂ) * Complex.I) ∂P := by
    apply integral_congr_ae
    filter_upwards [hdecomp n k hk] with ω hω
    rw [hω]
  rw [hphase] at hstep
  have hexponent : -(duration / ((n + 1 : ℕ) : ℝ) * c / 2) =
      -(duration / ((n + 1 : ℕ) : ℝ)) * (c / 2) := by ring
  rw [hexponent] at hstep
  simpa only [mul_comm] using hstep

theorem hasLaw_and_indep_of_gaussian_perturbations
    {Ω T E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [mE : MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [IsFiniteMeasure ν]
    (Z : T → Ω → E) (s t : T) (τ : ℕ → ℕ → T)
    (past : ℕ → ℕ → MeasurableSpace Ω) (basePast : MeasurableSpace Ω)
    (hpast : ∀ n k, past n k ≤ mΩ) (hbase : ∀ n k, basePast ≤ past n k)
    (hZstart : Measurable[basePast] (Z s))
    (hZpast : ∀ n k, Measurable[past n k] (Z (τ n k)))
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (duration : ℝ) (hduration : 0 ≤ duration) (c L : E → ℝ)
    (hc : ∀ θ, 0 ≤ c θ) (hL : ∀ θ, 0 ≤ L θ)
    (hchar : ∀ θ, charFun ν θ = (Real.exp (-duration * (c θ / 2)) : ℂ))
    (Q R : E → ℕ → ℕ → Ω → ℝ) (variance : E → ℕ → ℕ → ℝ≥0)
    (hLaw : ∀ θ n k, k < n + 1 →
      HasLaw (Q θ n k) (gaussianReal 0 (variance θ n k)) P)
    (hvariance : ∀ θ n k, k < n + 1 →
      (variance θ n k : ℝ) = (duration / ((n + 1 : ℕ) : ℝ)) * c θ)
    (hR : ∀ θ n k, k < n + 1 → AEStronglyMeasurable[mΩ] (R θ n k) P)
    (hRbound : ∀ θ n k, k < n + 1 → ∀ᵐ ω ∂P,
      |R θ n k ω| ≤ (duration / ((n + 1 : ℕ) : ℝ)) * L θ)
    (hdecomp : ∀ θ n k, k < n + 1 → ∀ᵐ ω ∂P,
      inner ℝ (Z (τ n (k + 1)) ω - Z (τ n k) ω) θ = Q θ n k ω + R θ n k ω)
    (hIndep : ∀ θ n k, k < n + 1 → ∀ K : Ω → ℂ,
      Measurable[past n k] K → IndepFun K (Q θ n k) P)
    (hmean : ∀ θ n k, k < n + 1 → ∀ K : Ω → ℂ,
      Measurable[past n k] K → (∀ ω, ‖K ω‖ ≤ 1) →
      (∫ ω, K ω * ((inner ℝ (Z (τ n (k + 1)) ω - Z (τ n k) ω) θ : ℝ) : ℂ) ∂P) = 0) :
    HasLaw (fun ω => Z t ω - Z s ω) ν P ∧
      Indep (MeasurableSpace.comap (fun ω => Z t ω - Z s ω) mE) basePast P := by
  let : MeasurableSpace Ω := mΩ
  have hbΩ : basePast ≤ mΩ := (hbase 0 0).trans (hpast 0 0)
  have hZs : Measurable (Z s) := hZstart.mono hbΩ le_rfl
  have hZt : Measurable (Z t) := by
    simpa only [hfinish 0] using (hZpast 0 1).mono (hpast 0 1) le_rfl
  apply InnovationLawIdentification.hasLaw_and_indep_of_restricted_integral
    P ν (fun ω => Z t ω - Z s ω) (hZt.sub hZs) basePast hbΩ
  intro A hA θ
  have hscalar := restricted_characteristic_of_gaussian_perturbations
    (fun r ω => inner ℝ (Z r ω) θ) s t τ past hpast (hbΩ A hA)
    (fun n k => hbase n k A hA)
    (fun n k => by
      have hZ := hZstart.mono (hbase n k) le_rfl
      fun_prop)
    (fun n k => by
      have hZ := hZpast n k
      fun_prop)
    hstart hfinish duration (c θ) (L θ) hduration (hc θ) (hL θ)
    (Q θ) (R θ) (variance θ) (hLaw θ) (hvariance θ) (hR θ) (hRbound θ)
    (by simpa only [inner_sub_left] using hdecomp θ) (hIndep θ)
    (by simpa only [inner_sub_left] using hmean θ)
  simpa only [hchar θ, inner_sub_left, Measure.real, mul_comm] using hscalar

end Problem336.InnovationGaussianProcess

end

end OAI
