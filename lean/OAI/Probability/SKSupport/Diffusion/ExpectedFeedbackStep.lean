import Mathlib
import OAI.Probability.SKSupport.Foundations.ControlledState
import OAI.Probability.SKSupport.Foundations.ElementaryControl

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma expected_feedback_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h c : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) {F D : ℝ → ℝ → ℝ} (hf : ∀ t, ContDiff ℝ 3 (F t))
    (C₂ C₃ Ct L : ℝ≥0) (hC₁ : ∀ t z, |deriv (F t) z| ≤ 1)
    (hC₂ : ∀ t z, |deriv (deriv (F t)) z| ≤ C₂)
    (hC₃ : ∀ t z, |iteratedDeriv 3 (F t) z| ≤ C₃)
    (hDm : Measurable (D s)) (hCt : ∀ z, |D s z| ≤ Ct)
    (hD : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z)
        (Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ))) r)
    (hL : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z y,
      |D r z-D s y| ≤ (L:ℝ)*(|r-(s:ℝ)|+|z-y|))
    (hPDE : ∀ z, D s z+(1/2:ℝ)*deriv (deriv (F s)) z+
      (c:ℝ)/2*(deriv (F s) z)^2 = 0) :
    |(∫ ω, F ((s:ℝ)+(h:ℝ))
        (Y ω+(B (s+h) ω-B s ω)+(c:ℝ)*(h:ℝ)*deriv (F s) (Y ω)) ∂P) -
      (∫ ω, F s (Y ω) ∂P) -
      (c:ℝ)*(h:ℝ)/2*(∫ ω, (deriv (F s) (Y ω))^2 ∂P)| ≤
        verificationError c C₂ C₃ L h := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hfd : ContDiff ℝ 2 (deriv (F s)) := (hf s).deriv'
  have hfm : Measurable (fun ω => deriv (F s) (Y ω)) := hfd.continuous.measurable.comp hYm
  let A (ω : Ω) := (c:ℝ)*(h:ℝ)*deriv (F s) (Y ω)
  have hAm : Measurable A := hfm.const_mul _
  have hAb : ∀ ω, |A ω| ≤ (c:ℝ)*(h:ℝ) := by
    intro ω
    dsimp only [A]
    rw [abs_mul, abs_mul, abs_of_nonneg c.coe_nonneg, abs_of_nonneg h.coe_nonneg]
    nlinarith [mul_le_mul_of_nonneg_left (hC₁ s (Y ω)) (mul_nonneg c.coe_nonneg h.coe_nonneg)]
  have hG := expected_time_space_step hB hm s h hY hYi hAm c hAb hf
    1 C₂ C₃ Ct L hC₁ hC₂ hC₃ hDm hCt hD hL
  have hui : Integrable (fun ω => (deriv (F s) (Y ω))^2) P := by
    apply Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (hC₁ s (Y ω)) 2
  have hDi : Integrable (fun ω => D s (Y ω)) P := Integrable.of_bound
    (hDm.comp hYm).aestronglyMeasurable Ct (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hCt (Y ω)))
  have hfdd : ContDiff ℝ 1 (deriv (deriv (F s))) := hfd.deriv'
  have hddi : Integrable (fun ω => deriv (deriv (F s)) (Y ω)) P := Integrable.of_bound
    (hfdd.continuous.measurable.comp hYm).aestronglyMeasurable C₂
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hC₂ s (Y ω)))
  have hPe : (∫ ω, D s (Y ω)+(1/2:ℝ)*deriv (deriv (F s)) (Y ω)+
      (c:ℝ)/2*(deriv (F s) (Y ω))^2 ∂P) = 0 := by
    have he : (fun ω => D s (Y ω)+(1/2:ℝ)*deriv (deriv (F s)) (Y ω)+
        (c:ℝ)/2*(deriv (F s) (Y ω))^2) = fun _ => (0:ℝ) := funext (fun ω => hPDE (Y ω))
    rw [he, integral_zero]
  have hsplit := integral_add (hDi.add (hddi.const_mul (1/2:ℝ))) (hui.const_mul ((c:ℝ)/2))
  simp only [Pi.add_apply] at hsplit
  rw [hsplit] at hPe
  have hsplit' := integral_add hDi (hddi.const_mul (1/2:ℝ))
  rw [hsplit', integral_const_mul, integral_const_mul] at hPe
  have hAe : (∫ ω, deriv (F s) (Y ω)*A ω ∂P) =
      (c:ℝ)*(h:ℝ)*(∫ ω, (deriv (F s) (Y ω))^2 ∂P) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp only [A]
    ring
  rw [hAe] at hG
  have hid : (c:ℝ)*(h:ℝ)*(∫ ω, (deriv (F s) (Y ω))^2 ∂P) +
      (h:ℝ)*((∫ ω, D s (Y ω) ∂P)+(1/2:ℝ)*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P)) =
      (c:ℝ)*(h:ℝ)/2*(∫ ω, (deriv (F s) (Y ω))^2 ∂P) := by
    have he := congrArg (fun z : ℝ => (h:ℝ)*z) hPe
    nlinarith
  rw [sub_sub] at hG
  rw [hid] at hG
  exact hG

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma feedback_controlledState_grid (hm : ∀ t, Measurable (B t)) (h c : ℝ≥0)
    {u : ℝ → ℝ → ℝ} (hum : ∀ t, Measurable (u t)) (hub : ∀ t z, |u t z| ≤ 1)
    (x : ℝ) (n k : ℕ) (hk : k ≤ n) (ω : Ω) :
    controlledState B
        (elementaryControl h (fun i ω => u ((i:ℝ≥0)*h) (feedbackEuler B h c u x i ω)) n)
        c x ((k:ℝ≥0)*h) ω = feedbackEuler B h c u x k ω := by
  let a (i : ℕ) (ω : Ω) := u ((i:ℝ≥0)*h) (feedbackEuler B h c u x i ω)
  have hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (elementaryControl h a n) := elementaryControl_progressive _ h
        (fun i => (hum _).comp (feedbackEuler_adapted hm h c hum x i)) n
  have ham := progressive_joint_measurable _ hap
  have hab : ∀ t ω, |elementaryControl h a n t ω| ≤ 1 :=
    elementaryControl_bound h (fun i ω => hub _ _) n
  induction k with
  | zero => simp [controlledState_zero, feedbackEuler]
  | succ k IH =>
    have hk' : k < n := by omega
    have ht : ((k+1:ℕ):ℝ≥0)*h = (k:ℝ≥0)*h+h := by push_cast; ring
    change controlledState B (elementaryControl h a n) c x (((k+1:ℕ):ℝ≥0)*h) ω = _
    rw [ht, controlledState_increment ham hab c x ((k:ℝ≥0)*h) h ω]
    have he : stepDrift (fun r => elementaryControl h a n (Real.toNNReal r))
        ((k:ℝ≥0)*h) h c ω = (h:ℝ)*((c:ℝ)*a k ω) := by
      exact elementaryControl_integral_on_step h a n k hk' (fun z => (c:ℝ)*z) ω
    change stepDrift (fun r => elementaryControl h a n (Real.toNNReal r))
      (↑((k:ℝ≥0)*h)) h c ω = (h:ℝ)*((c:ℝ)*a k ω) at he
    have hIH : controlledState B (elementaryControl h a n) c x ((k:ℝ≥0)*h) ω =
        feedbackEuler B h c u x k ω := IH (by omega)
    rw [he, hIH]
    simp only [feedbackEuler, ht, a]
    ring

omit mΩ in
lemma elementary_stepCost (h c : ℝ≥0) (a : ℕ → Ω → ℝ) (n k : ℕ) (hk : k < n) (ω : Ω) :
    stepCost (fun r => elementaryControl h a n (Real.toNNReal r)) ((k:ℝ≥0)*h) h c ω =
      (c:ℝ)*(h:ℝ)/2*(a k ω)^2 := by
  unfold stepCost
  rw [elementaryControl_integral_on_step h a n k hk (fun z => (c:ℝ)*z^2) ω]
  ring

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma finite_feedback_verification (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (h c : ℝ≥0) (x : ℝ) (n : ℕ)
    {F D : ℝ → ℝ → ℝ} (hf : ∀ t, ContDiff ℝ 3 (F t))
    (C₂ C₃ Ct L : ℝ≥0) (hC₁ : ∀ t z, |deriv (F t) z| ≤ 1)
    (hC₂ : ∀ t z, |deriv (deriv (F t)) z| ≤ C₂)
    (hC₃ : ∀ t z, |iteratedDeriv 3 (F t) z| ≤ C₃)
    (hDm : ∀ t, Measurable (D t)) (hCt : ∀ t z, |D t z| ≤ Ct)
    (hD : ∀ r ∈ Set.Icc (0:ℝ) ((n:ℝ)*(h:ℝ)), ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z)
        (Set.Icc (0:ℝ) ((n:ℝ)*(h:ℝ))) r)
    (hL : ∀ r ∈ Set.Icc (0:ℝ) ((n:ℝ)*(h:ℝ)),
      ∀ s ∈ Set.Icc (0:ℝ) ((n:ℝ)*(h:ℝ)), ∀ z y,
      |D r z-D s y| ≤ (L:ℝ)*(|r-s|+|z-y|))
    (hPDE : ∀ t ∈ Set.Icc (0:ℝ) ((n:ℝ)*(h:ℝ)), ∀ z,
      D t z+(1/2:ℝ)*deriv (deriv (F t)) z+(c:ℝ)/2*(deriv (F t) z)^2 = 0) :
    let u := fun t => deriv (F t)
    let α := elementaryControl h (fun k ω =>
      u ((k:ℝ≥0)*h) (feedbackEuler B h c u x k ω)) n
    F 0 x - (n:ℝ)*verificationError c C₂ C₃ L h ≤
      (∫ ω, F ((n:ℝ)*(h:ℝ)) (controlledState B α c x ((n:ℝ≥0)*h) ω) ∂P) -
        (∫ ω, stepCost (fun r => α (Real.toNNReal r)) 0 ((n:ℝ)*(h:ℝ)) c ω ∂P) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let u := fun t => deriv (F t)
  let a (k : ℕ) (ω : Ω) := u ((k:ℝ≥0)*h) (feedbackEuler B h c u x k ω)
  let α := elementaryControl h a n
  have hum : ∀ t, Measurable (u t) := fun t => (show ContDiff ℝ 2 (deriv (F t)) from (hf t).deriv').continuous.measurable
  have hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α :=
    elementaryControl_progressive _ h (fun k => (hum _).comp (feedbackEuler_adapted hm h c hum x k)) n
  have ham := progressive_joint_measurable _ hap
  have hab : ∀ t ω, |α t ω| ≤ 1 := elementaryControl_bound h (fun k ω => hC₁ _ _) n
  let A (r : ℝ) := α (Real.toNNReal r)
  have hAm : Measurable (fun p : ℝ × Ω => A p.1 p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hAb : ∀ r ω, |A r ω| ≤ 1 := fun r ω => hab _ ω
  let Q (k : ℕ) := (∫ ω, F ((k:ℝ)*(h:ℝ)) (controlledState B α c x ((k:ℝ≥0)*h) ω) ∂P) -
    (∫ ω, stepCost A 0 ((k:ℝ)*(h:ℝ)) c ω ∂P)
  have hgrid (k : ℕ) (hk : k ≤ n) (ω : Ω) :
      controlledState B α c x ((k:ℝ≥0)*h) ω = feedbackEuler B h c u x k ω :=
    feedback_controlledState_grid hm h c hum hC₁ x n k hk ω
  have hstep (k : ℕ) (hk : k < n) : -(Q (k+1)) - (-(Q k)) - 0 ≤ verificationError c C₂ C₃ L h := by
    let s : ℝ≥0 := (k:ℝ≥0)*h
    have hs : (s:ℝ) ∈ Set.Icc (0:ℝ) ((n:ℝ)*(h:ℝ)) := by
      constructor
      · exact s.coe_nonneg
      · dsimp only [s]; push_cast; gcongr
    have hsub : Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)) ⊆ Set.Icc (0:ℝ) ((n:ℝ)*(h:ℝ)) := by
      intro r hr
      refine ⟨s.coe_nonneg.trans hr.1, hr.2.trans ?_⟩
      have hn : (k:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast (by omega : k+1 ≤ n)
      dsimp only [s]; push_cast
      nlinarith [mul_le_mul_of_nonneg_right hn h.coe_nonneg]
    have hg := expected_feedback_step hB hm s h c
      (controlledState_adapted hm hap c x s) (controlledState_integrable hB ham hab c x s)
      hf C₂ C₃ Ct L hC₁ hC₂ hC₃ (hDm s) (hCt s)
      (fun r hr z => (hD r (hsub hr) z).mono hsub)
      (fun r hr z y => hL r (hsub hr) s hs z y) (hPDE s hs)
    have ht : s+h = ((k+1:ℕ):ℝ≥0)*h := by dsimp only [s]; push_cast; ring
    have hnext (ω : Ω) : controlledState B α c x s ω+(B (s+h) ω-B s ω)+
        (c:ℝ)*(h:ℝ)*deriv (F s) (controlledState B α c x s ω) =
        controlledState B α c x (((k+1:ℕ):ℝ≥0)*h) ω := by
      rw [hgrid (k+1) (by omega)]
      change controlledState B α c x ((k:ℝ≥0)*h) ω+_+_ = _
      rw [hgrid k hk.le]
      simp only [feedbackEuler, ht, s, u, NNReal.coe_mul]
    have hK : (∫ ω, stepCost A 0 ((s:ℝ)+(h:ℝ)) c ω ∂P) =
        (∫ ω, stepCost A 0 s c ω ∂P)+
        (c:ℝ)*(h:ℝ)/2*(∫ ω, (deriv (F s) (controlledState B α c x s ω))^2 ∂P) := by
      have he : stepCost A 0 ((s:ℝ)+(h:ℝ)) c = fun ω =>
          stepCost A 0 s c ω+stepCost A s h c ω := funext (stepCost_add hAm hAb c s h)
      rw [he, integral_add (stepCost_integrable hAm hAb 0 s c s.coe_nonneg c.coe_nonneg)
        (stepCost_integrable hAm hAb s h c h.coe_nonneg c.coe_nonneg)]
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      have hh := elementary_stepCost h c a n k hk ω
      change stepCost A (s:ℝ) h c ω = (c:ℝ)*(h:ℝ)/2*(a k ω)^2 at hh
      rw [hh]
      congr 2
      change a k ω = u ((k:ℝ≥0)*h) (controlledState B α c x ((k:ℝ≥0)*h) ω)
      rw [hgrid k hk.le]
    have heF : (fun ω => F ((s:ℝ)+(h:ℝ))
        (controlledState B α c x s ω+(B (s+h) ω-B s ω)+
        (c:ℝ)*(h:ℝ)*deriv (F s) (controlledState B α c x s ω))) =
        fun ω => F (((k+1:ℕ):ℝ)*(h:ℝ)) (controlledState B α c x (((k+1:ℕ):ℝ≥0)*h) ω) := by
      funext ω
      rw [hnext]
      congr 1
      dsimp only [s]; push_cast; ring
    rw [heF] at hg
    have htime : ((k+1:ℕ):ℝ)*(h:ℝ) = (s:ℝ)+(h:ℝ) := by dsimp only [s]; push_cast; ring
    rw [htime] at hg
    dsimp only [Q]
    rw [htime, hK]
    have hleft := neg_le_of_abs_le hg
    dsimp only [s] at hleft ⊢
    push_cast at hleft ⊢
    linarith
  have hh := finite_mesh_verification (fun k => -Q k) (fun _ => 0) n
    (verificationError c C₂ C₃ L h) hstep
  simp only [Finset.sum_const_zero, sub_zero] at hh
  have hQ0 : Q 0 = F 0 x := by simp [Q, controlledState_zero, stepCost]
  rw [hQ0] at hh
  change F 0 x - _ ≤ Q n
  linarith

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
