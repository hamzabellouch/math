import Mathlib
import OAI.Probability.SphericalField.Heat.GeneratorBounds

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma heatLog_control_step_error (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (g : Jet3), ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      ∀ (s : ℝ≥0), s ≤ 1 → ∀ (X Z A : Ω → ℝ), AEMeasurable X P →
        HasLaw Z (gaussianReal 0 s) P → IndepFun X Z P → AEMeasurable A P →
        (∀ ω, |A ω| ≤ (L : ℝ)*s) →
        |(∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, heatLog s d g.f (X ω) ∂P) -
          (∫ ω, g.d1 (X ω)*A ω ∂P) + (d : ℝ)*(s : ℝ)/2 * (∫ ω, (g.d1 (X ω))^2 ∂P)| ≤
          (C : ℝ)*(s : ℝ)*Real.sqrt s := by
  obtain ⟨C,hC⟩ := heatLog_generator_uniform d C₀ C₁ C₂ C₃
  let M₁ := ∫ z : ℝ, |z| ∂gaussianReal 0 1
  let M₃ := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  have hM₁ : 0 ≤ M₁ := integral_nonneg (fun z => abs_nonneg z)
  have hM₃ : 0 ≤ M₃ := integral_nonneg (fun z => by positivity)
  let K := (C₂ : ℝ)*((L : ℝ)*M₁+(L : ℝ)^2/2) + (C₃ : ℝ)/6*M₃
  have hK : 0 ≤ K := by positivity
  refine ⟨⟨K+C, by positivity⟩, ?_⟩
  intro Ω _ P _ g h₀ h₁ h₂ h₃ s hs X Z A hX hZ hI hA hAK
  have hG := gaussian_drift_taylor_mean_bound g.f g.contDiff C₁ C₃ C₂ (L*s)
    (fun y => by rw [g.deriv_eq]; exact (g.d1.norm_coe_le_norm y).trans h₁)
    (fun y => by rw [g.deriv2_eq]; exact (g.d2.norm_coe_le_norm y).trans h₂)
    (fun y => by rw [g.deriv3_eq]; exact (g.d3.norm_coe_le_norm y).trans h₃)
    hX hZ hI hA (by simpa only [NNReal.coe_mul] using hAK)
  rw [g.deriv_eq, g.deriv2_eq] at hG
  have hs0 := s.coe_nonneg
  have hr0 := Real.sqrt_nonneg (s : ℝ)
  have hr1 : Real.sqrt (s : ℝ) ≤ 1 := Real.sqrt_le_one.mpr hs
  have hsr : (s : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith [Real.sq_sqrt hs0]
  have hrcube : (Real.sqrt (s : ℝ))^3 = (s : ℝ)*Real.sqrt s := by nlinarith [Real.sq_sqrt hs0]
  have hG' : |(∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (∫ ω, g.d1 (X ω)*A ω ∂P) - (s : ℝ)/2*(∫ ω, g.d2 (X ω) ∂P)| ≤
      K*(s : ℝ)*Real.sqrt s := by
    refine hG.trans ?_
    simp only [NNReal.coe_mul, hrcube]
    have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsr hs0)
      (show 0 ≤ (C₂ : ℝ)*(L : ℝ)^2/2 by positivity)
    dsimp [K,M₁,M₃] at *
    nlinarith only [ht]
  have hiF := boundedContinuousFunction_integrable_comp g.f hX
  have hiH := boundedContinuousFunction_integrable_comp (heatLogBCF s d g.f) hX
  change Integrable (fun ω => heatLog s d g.f (X ω)) P at hiH
  have hi₂ := boundedContinuousFunction_integrable_comp g.d2 hX
  have hi₁₂ := boundedContinuousFunction_integrable_comp (g.d1^2) hX
  change Integrable (fun ω => (g.d1 (X ω))^2) P at hi₁₂
  let R := fun ω => heatLog s d g.f (X ω) - g.f (X ω) -
    (s : ℝ)/2*(g.d2 (X ω)+(d : ℝ)*(g.d1 (X ω))^2)
  have hR : |∫ ω, R ω ∂P| ≤ (C : ℝ)*(s : ℝ)*Real.sqrt s := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (f := R) (μ := P) (Filter.Eventually.of_forall fun ω =>
        show ‖R ω‖ ≤ (C : ℝ)*(s : ℝ)*Real.sqrt s by
          simpa only [Real.norm_eq_abs, R] using hC g h₀ h₁ h₂ h₃ s hs (X ω))
  have hRe : (∫ ω, R ω ∂P) = (∫ ω, heatLog s d g.f (X ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (s : ℝ)/2*((∫ ω, g.d2 (X ω) ∂P)+(d : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P)) := by
    have he := integral_sub (hiH.sub hiF) ((hi₂.add (hi₁₂.const_mul d)).const_mul ((s : ℝ)/2))
    simp only [Pi.sub_apply, Pi.add_apply] at he
    dsimp only [R]
    rw [he, integral_sub hiH hiF, integral_const_mul, integral_add hi₂ (hi₁₂.const_mul d), integral_const_mul]
  rw [hRe] at hR
  have hh := abs_sub
    ((∫ ω, g.f (X ω+Z ω+A ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (∫ ω, g.d1 (X ω)*A ω ∂P) - (s : ℝ)/2*(∫ ω, g.d2 (X ω) ∂P))
    ((∫ ω, heatLog s d g.f (X ω) ∂P) - (∫ ω, g.f (X ω) ∂P) -
      (s : ℝ)/2*((∫ ω, g.d2 (X ω) ∂P)+(d : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P)))
  have hh' := hh.trans (add_le_add hG' hR)
  convert! hh' using 1
  · congr 1; ring
  · change (K+(C : ℝ))*(s : ℝ)*Real.sqrt s = K*(s : ℝ)*Real.sqrt s + (C : ℝ)*(s : ℝ)*Real.sqrt s
    ring

lemma usualBrownianSigma_mono (P : Measure BrownianPath) {s t : Time} (hst : s ≤ t) :
    usualBrownianSigma P s ≤ usualBrownianSigma P t := by
  apply le_iInf
  intro r
  exact iInf_le_of_le (⟨r.val, lt_of_le_of_lt hst r.property⟩ : {r : ℝ≥0 // (s : ℝ) < r}) le_rfl

lemma brownianEval_usual_measurable (P : Measure BrownianPath) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ)
      (brownianEval ⟨t.val,t.property.1⟩) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro r
  apply le_sup_of_le_left
  exact le_iSup_of_le (⟨⟨t.val,t.property.1⟩, r.property.le⟩ : {s : ℝ≥0 // s ≤ r.val}) le_rfl

lemma progressive_prefix_integral_measurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (a : Time → ℝ) (ha : Measurable a) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ)
      (fun ω => ∫ r in Set.Iic t, a r * v r ω ∂timeLaw) := by
  let : MeasurableSpace BrownianPath := usualBrownianSigma P t
  have hm : Measurable (fun p : Set.Iic t × BrownianPath => a p.1.val * v p.1.val p.2) :=
    (ha.comp (measurable_subtype_coe.comp measurable_fst)).mul (hv t)
  have hi := hm.stronglyMeasurable.integral_prod_left (f := fun r ω => a r.val * v r.val ω) (μ := Measure.comap Subtype.val timeLaw)
  have he : (fun ω => ∫ r : Set.Iic t, a r.val * v r.val ω ∂Measure.comap Subtype.val timeLaw) =
      (fun ω => ∫ r in Set.Iic t, a r * v r ω ∂timeLaw) := by
    funext ω
    exact integral_subtype_comap (μ := timeLaw) (s := Set.Iic t) measurableSet_Iic (fun r => a r * v r ω)
  rw [he] at hi
  exact hi.measurable

lemma progressive_interval_integral_aemeasurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (a : Time → ℝ) (ha : Measurable a) (s t : Time) :
    AEMeasurable (fun ω => ∫ r in Set.Ioc s t, a r * v r ω ∂timeLaw) P := by
  have hm := (ha.comp measurable_fst).mul (progressive_joint_complete P hv)
  have hi := hm.stronglyMeasurable.integral_prod_left (β := NullMeasurableSpace BrownianPath P)
    (f := fun r ω => a r * v r ω) (μ := timeLaw.restrict (Set.Ioc s t))
  exact (show NullMeasurable (fun ω => ∫ r in Set.Ioc s t, a r * v r ω ∂timeLaw) P from hi.measurable).aemeasurable

def controlledPrefix (m : Trial) (v : Time → BrownianPath → ℝ) (t : Time) (ω : BrownianPath) : ℝ :=
  brownianEval ⟨t.val,t.property.1⟩ ω + ∫ r in Set.Iic t, m r * v r ω ∂timeLaw

lemma controlledPrefix_usual_measurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (t : Time) :
    @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) (controlledPrefix m v t) :=
  (brownianEval_usual_measurable P t).add (progressive_prefix_integral_measurable P hv m m.measurable t)

def timeSpan (s t : Time) : ℝ≥0 := Real.toNNReal ((t : ℝ)-(s : ℝ))

lemma timeSpan_coe {s t : Time} (hst : s ≤ t) :
    (timeSpan s t : ℝ) = (t : ℝ)-(s : ℝ) := Real.coe_toNNReal _ (sub_nonneg.mpr hst)

lemma timeSpan_le_one (s t : Time) : timeSpan s t ≤ 1 := by
  apply Real.toNNReal_le_one.mpr
  linarith [t.property.2,s.property.1]

end SphericalPerceptron
end
end

end OAI
