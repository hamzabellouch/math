import Mathlib
import OAI.Probability.Perceptron.Variational.HeatLogBCF

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
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
  have hiR : Integrable R P := (hiH.sub hiF).sub ((hi₂.add (hi₁₂.const_mul d)).const_mul ((s : ℝ)/2))
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

lemma timeLaw_real_Ioc {s t : Time} (hst : s ≤ t) :
    timeLaw.real (Set.Ioc s t) = (t : ℝ)-(s : ℝ) := by
  simp only [timeLaw_eq_volume, Measure.real, unitInterval.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]

lemma timeLaw_integral_const_Ioc {s t : Time} (hst : s ≤ t) (a : ℝ) :
    (∫ _r in Set.Ioc s t, a ∂timeLaw) = ((t : ℝ)-(s : ℝ))*a := by
  rw [integral_const, Measure.real, Measure.restrict_apply_univ, ← Measure.real,
    timeLaw_real_Ioc hst, smul_eq_mul]

lemma bounded_control_integrable (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    Integrable (fun r => m r * v r ω^2) timeLaw ∧ Integrable (fun r => m r * v r ω) timeLaw :=
  weightedTime_integrable m (progressive_time_measurable P hv ω)
    ((pathControlCost_le_bound m L hL ω).trans_lt (by finiteness))

lemma controlledPrefix_increment (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    controlledPrefix m v t ω = controlledPrefix m v s ω +
      (brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω) +
      ∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw := by
  have hi := (bounded_control_integrable P m L hv hL ω).2
  have he := setIntegral_union (s := Set.Iic s) (t := Set.Ioc s t)
    (Set.Iic_disjoint_Ioc (a := s) (c := t) le_rfl) measurableSet_Ioc
    hi.integrableOn hi.integrableOn
  rw [Set.Iic_union_Ioc_eq_Iic hst] at he
  unfold controlledPrefix
  rw [he]
  ring

lemma bounded_interval_drift (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    |∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw| ≤ (L : ℝ) * timeSpan s t := by
  rw [timeSpan_coe hst, mul_comm (L : ℝ)]
  calc
    _ ≤ ∫ r in Set.Ioc s t, |m r*v r ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ _r in Set.Ioc s t, (L : ℝ) ∂timeLaw := by
      apply integral_mono (bounded_control_integrable P m L hv hL ω).2.integrableOn.abs (integrable_const _)
      intro r
      change |m r * v r ω| ≤ (L : ℝ)
      rw [abs_mul, abs_of_nonneg (m.nonneg r)]
      exact (mul_le_mul_of_nonneg_left (hL r ω) (m.nonneg r)).trans
        (by nlinarith [m.le_one r])
    _ = _ := timeLaw_integral_const_Ioc hst L

def intervalControlCost (m : Trial) (v : Time → BrownianPath → ℝ) (s t : Time) (ω : BrownianPath) : ℝ :=
  ∫ r in Set.Ioc s t, m r * (v r ω)^2 ∂timeLaw

lemma intervalControlCost_nonneg (m : Trial) (v : Time → BrownianPath → ℝ) (s t : Time) (ω : BrownianPath) :
    0 ≤ intervalControlCost m v s t ω := integral_nonneg (fun r => mul_nonneg (m.nonneg r) (sq_nonneg _))

lemma intervalControlCost_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (s t : Time) :
    AEMeasurable (intervalControlCost m v s t) P :=
  progressive_interval_integral_aemeasurable P (fun r => (hv r).pow_const 2) m m.measurable s t

lemma intervalControlCost_le_bound (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (ω : BrownianPath) :
    intervalControlCost m v s t ω ≤ (L : ℝ)^2 * timeSpan s t := by
  rw [timeSpan_coe hst, mul_comm ((L : ℝ)^2)]
  calc
    _ ≤ ∫ _r in Set.Ioc s t, (L : ℝ)^2 ∂timeLaw := by
      apply integral_mono (bounded_control_integrable P m L hv hL ω).1.integrableOn (integrable_const _)
      intro r
      have hh : (v r ω)^2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) L.coe_nonneg).mpr (hL r ω)
      exact (mul_le_mul_of_nonneg_left hh (m.nonneg r)).trans (by nlinarith [m.le_one r])
    _ = _ := timeLaw_integral_const_Ioc hst _

lemma intervalControlCost_integrable (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hL : ∀ t ω, |v t ω| ≤ L) {s t : Time} (hst : s ≤ t) :
    Integrable (intervalControlCost m v s t) P :=
  bounded_real_integrable (intervalControlCost_aemeasurable P m hv s t) ((L : ℝ)^2*timeSpan s t)
    (Filter.Eventually.of_forall fun ω => by
      rw [abs_of_nonneg (intervalControlCost_nonneg m v s t ω)]
      exact intervalControlCost_le_bound P m L hv hL hst ω)

lemma interval_square_completion (P : Measure BrownianPath) (m : Trial) (L d : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ t ω, |v t ω| ≤ L)
    {s t : Time} (hst : s ≤ t) (hm : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ))
    (a : ℝ) (ω : BrownianPath) :
    2*a*(∫ r in Set.Ioc s t, m r * v r ω ∂timeLaw) -
      (d : ℝ)*(timeSpan s t : ℝ)*a^2 ≤ intervalControlCost m v s t ω := by
  have hi := bounded_control_integrable P m L hv hL ω
  have him : Integrable (fun r => m r) timeLaw := by
    apply (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (m.nonneg r)]; exact m.le_one r
  have hmono := setIntegral_mono_on (s := Set.Ioc s t) ((hi.2.const_mul (2*a)).sub (him.const_mul (a^2))).integrableOn
    hi.1.integrableOn measurableSet_Ioc (fun r _ => by
      change 2*a*(m r*v r ω) - a^2*m r ≤ m r*(v r ω)^2
      nlinarith [mul_nonneg (m.nonneg r) (sq_nonneg (v r ω-a))])
  have he : (∫ r in Set.Ioc s t, m r ∂timeLaw) = (d : ℝ)*timeSpan s t := by
    rw [setIntegral_congr_fun measurableSet_Ioc hm, timeLaw_integral_const_Ioc hst, timeSpan_coe hst, mul_comm]
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (hi.2.const_mul (2*a)).integrableOn (him.const_mul (a^2)).integrableOn,
    integral_const_mul, integral_const_mul, he] at hmono
  convert! hmono using 1
  ring

lemma brownian_increment_timeSpan (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {s t : Time} (hst : s ≤ t) :
    HasLaw (fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω)
      (gaussianReal 0 (timeSpan s t)) P := by
  have he : timeSpan s t = nndist (t : ℝ) (s : ℝ) := by
    apply NNReal.coe_injective
    rw [timeSpan_coe hst, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from hst))]
  rw [he]
  exact (hB.toIsPreBrownianReal.hasLaw_sub ⟨t.val,t.property.1⟩ ⟨s.val,s.property.1⟩).congr
    (Filter.Eventually.of_forall fun ω => rfl)

lemma brownian_control_cell_upper (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (P : Measure BrownianPath) [IsProbabilityMeasure P],
      IsBrownianReal brownianEval P → ∀ (m : Trial) (v : Time → BrownianPath → ℝ),
      Progressive P v → (∀ r ω, |v r ω| ≤ L) → ∀ (s t : Time), s < t →
      (∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) → ∀ (g : Jet3),
      ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      (∫ ω, g.f (controlledPrefix m v t ω) ∂P) -
        (∫ ω, heatLog (timeSpan s t) d g.f (controlledPrefix m v s ω) ∂P) ≤
        (∫ ω, intervalControlCost m v s t ω ∂P)/2 +
          (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) := by
  obtain ⟨C,hC⟩ := heatLog_control_step_error d L C₀ C₁ C₂ C₃
  refine ⟨C, ?_⟩
  intro P _ hB m v hv hL s t hst hm g h₀ h₁ h₂ h₃
  let X := controlledPrefix m v s
  let Z := fun ω => brownianEval ⟨t.val,t.property.1⟩ ω - brownianEval ⟨s.val,s.property.1⟩ ω
  let A := fun ω => ∫ r in Set.Ioc s t, m r*v r ω ∂timeLaw
  have hX := controlledPrefix_usual_measurable P m hv s
  have hXm : AEMeasurable X P := usual_measurable_aemeasurable P s hX
  have hAm : AEMeasurable A P := progressive_interval_integral_aemeasurable P hv m m.measurable s t
  have hAb : ∀ ω, |A ω| ≤ (L : ℝ)*timeSpan s t := bounded_interval_drift P m L hv hL hst.le
  have he := hC P g h₀ h₁ h₂ h₃ (timeSpan s t) (timeSpan_le_one s t) X Z A hXm
    (brownian_increment_timeSpan P hB hst.le)
    (brownian_increment_indep_adapted P hB s ⟨t.val,t.property.1⟩ hst hX) hAm hAb
  have hXT : ∀ ω, X ω+Z ω+A ω = controlledPrefix m v t ω := by
    intro ω
    exact (controlledPrefix_increment P m L hv hL hst.le ω).symm
  simp only [hXT] at he
  have hi₁ := boundedContinuousFunction_integrable_comp g.d1 hXm
  have hi₂ := boundedContinuousFunction_integrable_comp (g.d1^2) hXm
  change Integrable (fun ω => (g.d1 (X ω))^2) P at hi₂
  have hiA := bounded_real_integrable hAm ((L : ℝ)*timeSpan s t) (Filter.Eventually.of_forall hAb)
  have hiJ : Integrable (fun ω => g.d1 (X ω)*A ω) P :=
    hiA.bdd_mul ((g.d1.continuous.measurable.comp_aemeasurable hXm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => g.d1.norm_coe_le_norm (X ω))
  have hq := integral_mono ((hiJ.const_mul 2).sub (hi₂.const_mul ((d : ℝ)*(timeSpan s t : ℝ))))
    (intervalControlCost_integrable P m L hv hL hst.le)
    (fun ω => by
      change 2*(g.d1 (X ω)*A ω) - (d : ℝ)*(timeSpan s t : ℝ)*(g.d1 (X ω))^2 ≤ _
      nlinarith only [interval_square_completion P m L d hv hL hst.le hm (g.d1 (X ω)) ω])
  simp only [Pi.sub_apply] at hq
  rw [integral_sub (hiJ.const_mul 2) (hi₂.const_mul ((d : ℝ)*(timeSpan s t : ℝ))),
    integral_const_mul, integral_const_mul] at hq
  exact le_trans (by linarith only [(abs_le.mp he).2,hq]) le_rfl

lemma antitoneOn_of_superlinear_increment (F : Time → ℝ) (C : ℝ)
    {a b : Time} (hab : a ≤ b)
    (h : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      F t - F s ≤ C*((t : ℝ)-(s : ℝ))*Real.sqrt ((t : ℝ)-(s : ℝ))) : F b ≤ F a := by
  have hbnd : ∀ n : ℕ, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      F t - F s ≤ C*((t : ℝ)-(s : ℝ))*Real.sqrt (((t : ℝ)-(s : ℝ))*(1/2 : ℝ)^n) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro s hs t ht hst
      have hstreal : (s : ℝ) < (t : ℝ) := hst
      let u : Time := ⟨((s : ℝ)+(t : ℝ))/2, by
        constructor <;> linarith [s.property.1,s.property.2,t.property.1,t.property.2]⟩
      have hsu : s < u := by change (s : ℝ) < ((s : ℝ)+(t : ℝ))/2; linarith only [hstreal]
      have hut : u < t := by change ((s : ℝ)+(t : ℝ))/2 < (t : ℝ); linarith only [hstreal]
      have hu : u ∈ Set.Icc a b := ⟨hs.1.trans hsu.le,hut.le.trans ht.2⟩
      have h₁ := ih s hs u hu hsu
      have h₂ := ih u hu t ht hut
      have e₁ : (u : ℝ)-(s : ℝ) = ((t : ℝ)-(s : ℝ))/2 := by dsimp [u]; ring
      have e₂ : (t : ℝ)-(u : ℝ) = ((t : ℝ)-(s : ℝ))/2 := by dsimp [u]; ring
      rw [e₁] at h₁
      rw [e₂] at h₂
      have e₃ : ((t : ℝ)-(s : ℝ))*(1/2 : ℝ)^(n+1) = (((t : ℝ)-(s : ℝ))/2)*(1/2 : ℝ)^n := by rw [pow_succ]; ring
      rw [e₃]
      linarith only [h₁,h₂]
  rcases hab.eq_or_lt with heq | hlt
  · simp [heq]
  have hlim : Tendsto (fun n : ℕ => C*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))*(1/2 : ℝ)^n)) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    simpa using (hp.const_mul ((b : ℝ)-(a : ℝ))).sqrt.const_mul (C*((b : ℝ)-(a : ℝ)))
  have he := ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hbnd n a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hlt)
  linarith only [he]

lemma timeSpan_add {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) :
    timeSpan a b + timeSpan b c = timeSpan a c := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add,timeSpan_coe hab,timeSpan_coe hbc,timeSpan_coe (hab.trans hbc)]
  ring

lemma intervalControlCost_add (P : Measure BrownianPath) (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) (ω : BrownianPath) :
    intervalControlCost m v a c ω = intervalControlCost m v a b ω + intervalControlCost m v b c ω := by
  have hi := (bounded_control_integrable P m L hv hL ω).1
  have he := setIntegral_union (s := Set.Ioc a b) (t := Set.Ioc b c)
    (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi.integrableOn hi.integrableOn
  rwa [Set.Ioc_union_Ioc_eq_Ioc hab hbc] at he

lemma expected_intervalControlCost_add (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hL : ∀ r ω, |v r ω| ≤ L) {a b c : Time} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ ω, intervalControlCost m v a c ω ∂P) =
      (∫ ω, intervalControlCost m v a b ω ∂P) + (∫ ω, intervalControlCost m v b c ω ∂P) := by
  simp only [intervalControlCost_add P m L hv hL hab hbc]
  exact integral_add (intervalControlCost_integrable P m L hv hL hab)
    (intervalControlCost_integrable P m L hv hL hbc)

lemma brownian_control_interval_upper (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (L d : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {a b : Time} (hab : a ≤ b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ)) (g : Jet3) :
    (∫ ω, g.f (controlledPrefix m v b ω) ∂P) -
      (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) ≤
      (∫ ω, intervalControlCost m v a b ω ∂P)/2 := by
  obtain ⟨C₀,C₁,C₂,C₃,hG⟩ := g.heatLog_uniform_bounds d
  obtain ⟨C,hC⟩ := brownian_control_cell_upper d L C₀ C₁ C₂ C₃
  let F : Time → ℝ := fun t =>
    (∫ ω, heatLog (timeSpan t b) d g.f (controlledPrefix m v t ω) ∂P) -
      (∫ ω, intervalControlCost m v a t ω ∂P)/2
  have hF := antitoneOn_of_superlinear_increment F (C : ℝ) hab (by
    intro s hs t ht hst
    have hmst : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ) := fun r hr => hm r ⟨hs.1.trans_lt hr.1,hr.2.trans ht.2⟩
    obtain ⟨h₀,h₁,h₂,h₃⟩ := hG (timeSpan t b)
    have hh := hC P hB m v hv hL s t hst hmst (g.heatLog (timeSpan t b) d) h₀ h₁ h₂ h₃
    rw [g.heatLog_f] at hh
    simp only [heatLogBCF_coe, heatLog_semigroup, timeSpan_add hst.le ht.2] at hh
    have hcost := expected_intervalControlCost_add P m L hv hL hs.1 hst.le
    rw [timeSpan_coe hst.le] at hh
    dsimp [F]
    linarith only [hh,hcost])
  have he₁ : timeSpan b b = 0 := by simp [timeSpan]
  have he₂ : ∀ ω, intervalControlCost m v a a ω = 0 := by intro ω; simp [intervalControlCost]
  dsimp [F] at hF
  simp only [he₁,heatLog_zero,he₂,integral_zero,zero_div,sub_zero] at hF
  linarith only [hF]

def patchControl (v : Time → BrownianPath → ℝ) (s t : Time) (a : BrownianPath → ℝ) :
    Time → BrownianPath → ℝ := fun r ω => if r ∈ Set.Ioc s t then a ω else v r ω

lemma progressive_patchControl (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (s t : Time)
    {a : BrownianPath → ℝ} (ha : @Measurable _ _ (usualBrownianSigma P s) (borel ℝ) a) :
    Progressive P (patchControl v s t a) := by
  intro T
  by_cases hs : s ≤ T
  · have haT := ha.mono (usualBrownianSigma_mono P hs) le_rfl
    apply Measurable.ite _ (haT.comp measurable_snd) (hv T)
    exact (measurableSet_Ioc : MeasurableSet (Set.Ioc s t)).preimage
      (measurable_subtype_coe.comp measurable_fst)
  · have he : (fun p : Set.Iic T × BrownianPath => patchControl v s t a p.1.val p.2) =
        (fun p : Set.Iic T × BrownianPath => v p.1.val p.2) := by
      funext p
      apply ite_eq_right
      intro h
      exact hs (h.1.le.trans p.1.property)
    rw [he]
    exact hv T

lemma patchControl_bound {v : Time → BrownianPath → ℝ} {L : ℝ≥0}
    (hv : ∀ r ω, |v r ω| ≤ L) (s t : Time) {a : BrownianPath → ℝ}
    (ha : ∀ ω, |a ω| ≤ L) : ∀ r ω, |patchControl v s t a r ω| ≤ L := by
  intro r ω
  simp only [patchControl]
  split <;> first | exact ha ω | exact hv r ω

end SphericalPerceptronFreeEnergy
end

end OAI
