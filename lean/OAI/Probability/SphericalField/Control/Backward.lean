import Mathlib
import OAI.Probability.SphericalField.Control.Feedback

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

end SphericalPerceptron
end
end

end OAI
