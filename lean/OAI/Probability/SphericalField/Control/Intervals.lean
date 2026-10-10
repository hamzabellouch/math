import Mathlib
import OAI.Probability.SphericalField.Control.StepError

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

end SphericalPerceptron
end
end

end OAI
