import Mathlib
import OAI.Probability.Perceptron.Control.ControlledPrefix

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

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

def backwardScore (P : Measure BrownianPath) (m : Trial) (v : Time → BrownianPath → ℝ)
    (a b : Time) (d : ℝ≥0) (g : Jet3) (t : Time) : ℝ :=
  (∫ ω, heatLog (timeSpan t b) d g.f (controlledPrefix m v t ω) ∂P) -
    (∫ ω, intervalControlCost m v a t ω ∂P)/2

lemma brownian_control_patch_gain (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ)) :
    ∃ L C : ℝ≥0, L₀ ≤ L ∧ ∀ (v : Time → BrownianPath → ℝ), Progressive P v →
      (∀ r ω, |v r ω| ≤ L) → ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s < t →
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc s t, ∀ ω, w r ω = v r ω) ∧
        backwardScore P m v a b d g s - (C : ℝ)*(timeSpan s t : ℝ)*Real.sqrt (timeSpan s t) ≤
          backwardScore P m w a b d g t := by
  obtain ⟨C₀,C₁,C₂,C₃,hG⟩ := g.heatLog_uniform_bounds d
  let L := max L₀ C₁
  obtain ⟨C,hC⟩ := brownian_control_feedback_cell d L C₀ C₁ C₂ C₃
  refine ⟨L,C,le_max_left _ _,?_⟩
  intro v hv hL s hs t ht hst
  let j := g.heatLog (timeSpan t b) d
  let A := fun ω => j.d1 (controlledPrefix m v s ω)
  have hAm : @Measurable _ _ (usualBrownianSigma P s) (borel ℝ) A :=
    j.d1.continuous.measurable.comp (controlledPrefix_usual_measurable P m hv s)
  obtain ⟨h₀,h₁,h₂,h₃⟩ := hG (timeSpan t b)
  have hAL : ∀ ω, |A ω| ≤ L := fun ω =>
    ((j.d1.norm_coe_le_norm _).trans h₁).trans (show (C₁ : ℝ) ≤ L from le_max_right _ _)
  let w := patchControl v s t A
  have hw : Progressive P w := progressive_patchControl P hv s t hAm
  have hwL : ∀ r ω, |w r ω| ≤ L := patchControl_bound hL s t hAL
  have hmst : ∀ r ∈ Set.Ioc s t, m r = (d : ℝ) := fun r hr => hm r ⟨hs.1.trans_lt hr.1,hr.2.trans ht.2⟩
  have hXe : ∀ ω, controlledPrefix m w s ω = controlledPrefix m v s ω :=
    patchControl_prefix m v s t A le_rfl
  have hQe : ∀ ω, intervalControlCost m w a s ω = intervalControlCost m v a s ω :=
    patchControl_cost_prefix m v s t A a le_rfl
  have hfeedback : ∀ r ∈ Set.Ioc s t, ∀ ω, w r ω = j.d1 (controlledPrefix m w s ω) := by
    intro r hr ω
    rw [hXe]
    exact ite_eq_left hr
  have hh := hC P hB m w hw hwL s t hst hmst j h₀ h₁ h₂ h₃ hfeedback
  change |(∫ ω, (g.heatLog (timeSpan t b) d).f (controlledPrefix m w t ω) ∂P) - _ - _| ≤ _ at hh
  rw [g.heatLog_f] at hh
  simp only [heatLogBCF_coe,heatLog_semigroup,timeSpan_add hst.le ht.2,hXe] at hh
  have hcost := expected_intervalControlCost_add P m L hw hwL hs.1 hst.le
  simp only [hQe] at hcost
  refine ⟨w,hw,hwL,?_,?_⟩
  · intro r hr ω
    exact ite_eq_right hr
  · dsimp [backwardScore]
    linarith only [(abs_le.mp hh).1,hcost]

def timeMesh (a b : Time) (n k : ℕ) : Time :=
  Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one ((k : ℝ)/(n+1)))

lemma timeMesh_coe (a b : Time) (n k : ℕ) (hk : k ≤ n+1) :
    (timeMesh a b n k : ℝ) = (a : ℝ)+((b : ℝ)-(a : ℝ))*((k : ℝ)/(n+1)) := by
  have hp : (0 : ℝ) < n+1 := by positivity
  have hh : (k : ℝ)/(n+1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hp).mpr
      exact_mod_cast hk
  simp only [timeMesh, Set.projIcc_of_mem zero_le_one hh, Set.Icc.coe_convexComb]
  ring

lemma timeMesh_zero (a b : Time) (n : ℕ) : timeMesh a b n 0 = a := by
  apply Subtype.ext
  rw [timeMesh_coe a b n 0 (Nat.zero_le _)]
  simp

lemma timeMesh_last (a b : Time) (n : ℕ) : timeMesh a b n (n+1) = b := by
  apply Subtype.ext
  rw [timeMesh_coe a b n (n+1) le_rfl]
  push_cast
  rw [div_self (by positivity : (n : ℝ)+1 ≠ 0)]
  ring

lemma timeMesh_between {a b : Time} (hab : a ≤ b) (n k : ℕ) (hk : k ≤ n+1) :
    timeMesh a b n k ∈ Set.Icc a b := by
  have hp : (0 : ℝ) < n+1 := by positivity
  have hq : 0 ≤ (k : ℝ)/(n+1) := by positivity
  have hr : (k : ℝ)/(n+1) ≤ 1 := (div_le_one hp).mpr (by exact_mod_cast hk)
  have habr : (a : ℝ) ≤ (b : ℝ) := hab
  constructor <;> change _ ≤ (show ℝ from ↑_)
  · rw [timeMesh_coe a b n k hk]
    nlinarith
  · rw [timeMesh_coe a b n k hk]
    nlinarith

lemma timeMesh_step {a b : Time} (hab : a < b) (n k : ℕ) (hk : k < n+1) :
    timeMesh a b n k < timeMesh a b n (k+1) := by
  change (timeMesh a b n k : ℝ) < (timeMesh a b n (k+1) : ℝ)
  rw [timeMesh_coe a b n k hk.le, timeMesh_coe a b n (k+1) hk]
  have hh : (a : ℝ) < (b : ℝ) := hab
  have hp : (0 : ℝ) < n+1 := by positivity
  apply add_lt_add_of_le_of_lt le_rfl
  apply mul_lt_mul_of_pos_left _ (sub_pos.mpr hh)
  apply div_lt_div_of_pos_right _ hp
  exact_mod_cast Nat.lt_succ_self k

lemma timeMesh_step_size (a b : Time) (n k : ℕ) (hk : k < n+1) :
    (timeMesh a b n (k+1) : ℝ) - (timeMesh a b n k : ℝ) = ((b : ℝ)-(a : ℝ))/(n+1) := by
  rw [timeMesh_coe a b n k hk.le,timeMesh_coe a b n (k+1) hk]
  push_cast
  ring

lemma brownian_control_interval_lower_mesh (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hab : a < b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ))
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hvL : ∀ r ω, |v r ω| ≤ L₀) :
    ∃ L C : ℝ≥0, L₀ ≤ L ∧ ∀ n : ℕ,
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
        (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) -
          (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)) ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  obtain ⟨L,C,hLL,hgain⟩ := brownian_control_patch_gain P hB m d L₀ g hm
  refine ⟨L,C,hLL,?_⟩
  intro n
  let τ := timeMesh a b n
  let δ : ℝ := ((b : ℝ)-(a : ℝ))/(n+1)
  let E : ℝ := (C : ℝ)*δ*Real.sqrt δ
  have hind : ∀ k : ℕ, k ≤ n+1 →
      ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
        (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
        backwardScore P m v a b d g a - (k : ℝ)*E ≤ backwardScore P m w a b d g (τ k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨v,hv,fun r ω => (hvL r ω).trans (show (L₀ : ℝ) ≤ L from hLL),?_,?_⟩
      · intro _ _ _; rfl
      · simp only [τ,timeMesh_zero,Nat.cast_zero,zero_mul,sub_zero,le_refl]
    | succ k ih =>
      intro hk
      obtain ⟨u,hu,huL,huout,huScore⟩ := ih (Nat.le_trans (Nat.le_succ k) hk)
      have hk' : k < n+1 := hk
      have hs := timeMesh_between hab.le n k hk'.le
      have ht := timeMesh_between hab.le n (k+1) hk
      have hst := timeMesh_step hab n k hk'
      obtain ⟨w,hw,hwL,hwout,hwScore⟩ := hgain u hu huL (τ k) hs (τ (k+1)) ht hst
      have heδ : (timeSpan (τ k) (τ (k+1)) : ℝ) = δ := by
        rw [timeSpan_coe hst.le]
        exact timeMesh_step_size a b n k hk'
      rw [heδ] at hwScore
      refine ⟨w,hw,hwL,?_,?_⟩
      · intro r hr ω
        have hr' : r ∉ Set.Ioc (τ k) (τ (k+1)) := fun hh =>
          hr ⟨hs.1.trans_lt hh.1,hh.2.trans ht.2⟩
        rw [hwout r hr' ω]
        exact huout r hr ω
      · change backwardScore P m u a b d g (τ k) - E ≤ _ at hwScore
        rw [Nat.cast_succ]
        linarith only [huScore,hwScore]
  obtain ⟨w,hw,hwL,hwout,hwScore⟩ := hind (n+1) le_rfl
  have he : ((n+1 : ℕ) : ℝ)*E =
      (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)) := by
    dsimp [E,δ]
    push_cast
    field_simp
  have hz : timeSpan b b = 0 := by simp [timeSpan]
  have hq : ∀ ω, intervalControlCost m v a a ω = 0 := by intro ω; simp [intervalControlCost]
  simp only [τ,timeMesh_last,he,backwardScore,hz,heatLog_zero,hq,integral_zero,zero_div,sub_zero] at hwScore
  exact ⟨w,hw,hwL,hwout,hwScore⟩

lemma brownian_control_interval_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial) (d L₀ : ℝ≥0) (g : Jet3)
    {a b : Time} (hab : a < b) (hm : ∀ r ∈ Set.Ioc a b, m r = (d : ℝ))
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hvL : ∀ r ω, |v r ω| ≤ L₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ≥0, ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ L) ∧
      (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
      (∫ ω, heatLog (timeSpan a b) d g.f (controlledPrefix m v a ω) ∂P) - ε ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  obtain ⟨L,C,_,hmesh⟩ := brownian_control_interval_lower_mesh P hB m d L₀ g hab hm v hv hvL
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => ((b : ℝ)-(a : ℝ))/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have he : Tendsto (fun n : ℕ => (C : ℝ)*((b : ℝ)-(a : ℝ))*Real.sqrt (((b : ℝ)-(a : ℝ))/(n+1)))
      atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hd).const_mul ((C : ℝ)*((b : ℝ)-(a : ℝ)))
  obtain ⟨n,hn⟩ := (he.eventually (gt_mem_nhds hε)).exists
  obtain ⟨w,hw,hwL,hwout,hwval⟩ := hmesh n
  exact ⟨L,w,hw,hwL,hwout,by linarith⟩

inductive HeatChain (m : Trial) (g : Jet3) : Time → Time → Jet3 → Prop
  | nil (a : Time) : HeatChain m g a a g
  | cons {a t b : Time} {h : Jet3} (d : ℝ≥0) (hat : a < t) (htb : t ≤ b)
      (hm : ∀ r ∈ Set.Ioc a t, m r = (d : ℝ)) (tail : HeatChain m g t b h) :
      HeatChain m g a b (h.heatLog (timeSpan a t) d)

lemma HeatChain.left_le_right {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) : a ≤ b := by
  cases H with
  | nil => exact le_rfl
  | cons _ hat htb _ _ => exact hat.le.trans htb

lemma controls_equal_prefix {m : Trial} {v w : Time → BrownianPath → ℝ} {a b r : Time}
    (h : ∀ t ∉ Set.Ioc a b, ∀ ω, w t ω = v t ω) (hr : r ≤ a) (ω : BrownianPath) :
    controlledPrefix m w r ω = controlledPrefix m v r ω := by
  unfold controlledPrefix
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro t ht
  dsimp only
  rw [h t (fun hh => not_lt_of_ge (ht.trans hr) hh.1) ω]

lemma controls_equal_cost_prefix {m : Trial} {v w : Time → BrownianPath → ℝ} {a b r s : Time}
    (h : ∀ t ∉ Set.Ioc a b, ∀ ω, w t ω = v t ω) (hr : r ≤ a) (ω : BrownianPath) :
    intervalControlCost m w s r ω = intervalControlCost m v s r ω := by
  unfold intervalControlCost
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [h t (fun hh => not_lt_of_ge (ht.2.trans hr) hh.1) ω]

lemma HeatChain.upper {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L) :
    (∫ ω, g.f (controlledPrefix m v b ω) ∂P) -
      (∫ ω, intervalControlCost m v a b ω ∂P)/2 ≤
        (∫ ω, h.f (controlledPrefix m v a ω) ∂P) := by
  induction H with
  | nil a => simp [intervalControlCost]
  | @cons a t b h d hat htb hm tail ih =>
    have hi := brownian_control_interval_upper P hB m L d hv hL hat.le hm h
    have hc := expected_intervalControlCost_add P m L hv hL hat.le htb
    rw [Jet3.heatLog_f]
    simp only [heatLogBCF_coe]
    linarith only [ih,hi,hc]

lemma HeatChain.lower {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ≥0, ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ K) ∧
      (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
      (∫ ω, h.f (controlledPrefix m v a ω) ∂P) - ε ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  induction H generalizing v L ε with
  | nil a =>
    refine ⟨L,v,hv,hL,fun _ _ _ => rfl,?_⟩
    simp only [intervalControlCost,Set.Ioc_self,Measure.restrict_empty,integral_zero_measure,
      integral_zero,zero_div,sub_zero]
    linarith
  | @cons a t b h d hat htb hm tail ih =>
    obtain ⟨K,u,hu,huK,huout,huval⟩ :=
      brownian_control_interval_lower P hB m d L h hat hm v hv hL (by positivity : 0 < ε/2)
    obtain ⟨K',w,hw,hwK,hwout,hwval⟩ := ih K u hu huK (by positivity : 0 < ε/2)
    have hc := expected_intervalControlCost_add P m K' hw hwK hat.le htb
    have he : ∀ ω, intervalControlCost m w a t ω = intervalControlCost m u a t ω :=
      controls_equal_cost_prefix hwout le_rfl
    simp only [he] at hc
    refine ⟨K',w,hw,hwK,?_,?_⟩
    · intro r hr ω
      rw [hwout r (fun hh => hr ⟨hat.trans hh.1,hh.2⟩) ω]
      exact huout r (fun hh => hr ⟨hh.1,hh.2.trans htb⟩) ω
    · rw [Jet3.heatLog_f]
      simp only [heatLogBCF_coe]
      linarith only [huval,hwval,hc]

lemma controlledPrefix_one (m : Trial) (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    controlledPrefix m v 1 ω = brownianEval 1 ω + controlDrift m v ω := by
  simp only [controlledPrefix,controlDrift,show Set.Iic (1 : Time) = Set.univ from Set.Iic_top,
    Measure.restrict_univ]
  rfl

lemma controlledPrefix_zero (P : Measure BrownianPath) (hB : IsBrownianReal brownianEval P)
    (m : Trial) (v : Time → BrownianPath → ℝ) : controlledPrefix m v 0 =ᵐ[P] fun _ => 0 := by
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  simp only [controlledPrefix,show Set.Iic (0 : Time) = {0} from Set.Iic_bot,
    Measure.restrict_singleton,measure_singleton,zero_smul,integral_zero_measure,add_zero]
  exact hω

lemma intervalControlCost_full (m : Trial) (v : Time → BrownianPath → ℝ)
    (ω : BrownianPath) (hm : Measurable (v · ω)) :
    intervalControlCost m v 0 1 ω = (pathControlCost m v ω).toReal := by
  unfold intervalControlCost
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := timeLaw)), show Set.Icc (0 : Time) 1 = Set.univ from Set.Icc_bot_top,
    Measure.restrict_univ]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun r => mul_nonneg (m.nonneg r) (sq_nonneg _))
    ((m.measurable.mul (hm.pow_const 2)).aestronglyMeasurable)

lemma expected_intervalControlCost_full (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, intervalControlCost m v 0 1 ω ∂P) = (controlCost P m v).toReal := by
  simp only [intervalControlCost_full m v _ (progressive_time_measurable P hv _)]
  exact integral_pathControlCost P m hv hc

lemma Jet3.lipschitz (g : Jet3) : LipschitzWith ‖g.d1‖₊ g.f := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (g.has1 x).differentiableAt)
  intro x
  rw [g.deriv_eq]
  exact_mod_cast g.d1.norm_coe_le_norm x

lemma HeatChain.controlValue_eq {m : Trial} {g h : Jet3}
    (H : HeatChain m g 0 1 h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) : controlValue P g.f m = h.f 0 := by
  apply le_antisymm
  · apply controlValue_le_of_bounded_controls P g.f m ‖g.d1‖₊ g.lipschitz
    intro v hv hc hL
    have hh := H.upper P hB ‖g.d1‖₊ hv hL
    have he : (∫ ω, h.f (controlledPrefix m v 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m v] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hv hc] at hh
    simp only [controlledPrefix_one] at hh
    exact hh
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨K,w,hw,hwK,_,hwval⟩ := H.lower P hB 0 (fun _ _ => 0) (progressive_zero P)
      (by simp) hε
    have hc : controlCost P m w < ∞ := (controlCost_le_bound P m K hwK).trans_lt (by finiteness)
    have he : (∫ ω, h.f (controlledPrefix m (fun _ _ => 0) 0 ω) ∂P) = h.f 0 := by
      calc
        _ = ∫ _ω : BrownianPath, h.f 0 ∂P := integral_congr_ae (by
          filter_upwards [controlledPrefix_zero P hB m (fun _ _ => 0)] with ω hω
          rw [hω])
        _ = _ := by simp
    rw [he,expected_intervalControlCost_full P m hw hc] at hwval
    simp only [controlledPrefix_one] at hwval
    have hsup : controlPayoff P g.f m w ≤ controlValue P g.f m :=
      le_csSup (controlPayoffs_bddAbove P g.f m) ⟨w,hw,hc,rfl⟩
    change h.f 0 - ε ≤ controlPayoff P g.f m w at hwval
    linarith

end SphericalPerceptronFreeEnergy
end

end OAI
