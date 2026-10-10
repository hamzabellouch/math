import Mathlib
import OAI.Probability.SphericalField.Control.Intervals

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

lemma patchControl_prefix (m : Trial) (v : Time → BrownianPath → ℝ)
    (s t : Time) (a : BrownianPath → ℝ) {r : Time} (hrs : r ≤ s) (ω : BrownianPath) :
    controlledPrefix m (patchControl v s t a) r ω = controlledPrefix m v r ω := by
  unfold controlledPrefix
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro u hu
  have hh : u ∉ Set.Ioc s t := fun h => (not_lt_of_ge (hu.trans hrs)) h.1
  simp only [patchControl,ite_eq_right hh]

lemma patchControl_cost_prefix (m : Trial) (v : Time → BrownianPath → ℝ)
    (s t : Time) (a : BrownianPath → ℝ) (q : Time) {r : Time} (hrs : r ≤ s) (ω : BrownianPath) :
    intervalControlCost m (patchControl v s t a) q r ω = intervalControlCost m v q r ω := by
  unfold intervalControlCost
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hh : u ∉ Set.Ioc s t := fun h => (not_lt_of_ge (hu.2.trans hrs)) h.1
  simp only [patchControl,ite_eq_right hh]

lemma patchControl_drift_cell (m : Trial) (v : Time → BrownianPath → ℝ)
    {s t : Time} (hst : s ≤ t) (a : BrownianPath → ℝ) (d : ℝ≥0)
    (hm : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) (ω : BrownianPath) :
    (∫ r in Set.Ioc s t, m r * patchControl v s t a r ω ∂timeLaw) =
      (d : ℝ)*(timeSpan s t : ℝ)*a ω := by
  have he : ∀ r ∈ Set.Ioc s t, m r * patchControl v s t a r ω = (d : ℝ)*a ω := by
    intro r hr
    rw [hm r hr,patchControl,ite_eq_left hr]
  rw [setIntegral_congr_fun measurableSet_Ioc he,timeLaw_integral_const_Ioc hst,timeSpan_coe hst]
  ring

lemma patchControl_cost_cell (m : Trial) (v : Time → BrownianPath → ℝ)
    {s t : Time} (hst : s ≤ t) (a : BrownianPath → ℝ) (d : ℝ≥0)
    (hm : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) (ω : BrownianPath) :
    intervalControlCost m (patchControl v s t a) s t ω =
      (d : ℝ)*(timeSpan s t : ℝ)*(a ω)^2 := by
  have he : ∀ r ∈ Set.Ioc s t, m r * (patchControl v s t a r ω)^2 = (d : ℝ)*(a ω)^2 := by
    intro r hr
    rw [hm r hr,patchControl,ite_eq_left hr]
  rw [intervalControlCost,setIntegral_congr_fun measurableSet_Ioc he,timeLaw_integral_const_Ioc hst,timeSpan_coe hst]
  ring

lemma brownian_control_feedback_cell (d L C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (P : Measure BrownianPath) [IsProbabilityMeasure P],
      IsBrownianReal brownianEval P → ∀ (m : Trial) (v : Time → BrownianPath → ℝ),
      Progressive P v → (∀ r ω, |v r ω| ≤ L) → ∀ (s t : Time), s < t →
      (∀ r ∈ Set.Ioc s t, m r = (d : ℝ)) → ∀ (g : Jet3),
      ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ → ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ →
      (∀ r ∈ Set.Ioc s t, ∀ ω, v r ω = g.d1 (controlledPrefix m v s ω)) →
      |(∫ ω, g.f (controlledPrefix m v t ω) ∂P) -
        (∫ ω, heatLog (timeSpan s t) d g.f (controlledPrefix m v s ω) ∂P) -
        (∫ ω, intervalControlCost m v s t ω ∂P)/2| ≤
          (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) := by
  obtain ⟨C,hC⟩ := heatLog_control_step_error d L C₀ C₁ C₂ C₃
  refine ⟨C, ?_⟩
  intro P _ hB m v hv hL s t hst hm g h₀ h₁ h₂ h₃ hV
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
  have hXT : ∀ ω, X ω+Z ω+A ω = controlledPrefix m v t ω := fun ω =>
    (controlledPrefix_increment P m L hv hL hst.le ω).symm
  simp only [hXT] at he
  have hA : ∀ ω, A ω = (d : ℝ)*(timeSpan s t : ℝ)*g.d1 (X ω) := by
    intro ω
    dsimp only [A]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hm r hr,hV r hr ω]),
      timeLaw_integral_const_Ioc hst.le, timeSpan_coe hst.le]
    ring
  have hQ : ∀ ω, intervalControlCost m v s t ω =
      (d : ℝ)*(timeSpan s t : ℝ)*(g.d1 (X ω))^2 := by
    intro ω
    rw [intervalControlCost,setIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hm r hr,hV r hr ω]),
      timeLaw_integral_const_Ioc hst.le, timeSpan_coe hst.le]
    ring
  have hJ : (∫ ω, g.d1 (X ω)*A ω ∂P) =
      (d : ℝ)*(timeSpan s t : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P) := by
    simp only [hA]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by ring
  have hQi : (∫ ω, intervalControlCost m v s t ω ∂P) =
      (d : ℝ)*(timeSpan s t : ℝ)*(∫ ω, (g.d1 (X ω))^2 ∂P) := by
    simp only [hQ,integral_const_mul]
  rw [hJ] at he
  rw [hQi]
  convert! he using 1
  congr 1
  ring

end SphericalPerceptron
end
end

end OAI
