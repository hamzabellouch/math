import Mathlib
import OAI.Probability.SKSupport.Foundations.ExpectedVerificationStep
import OAI.Probability.SKSupport.Diffusion.ProgressiveIntegralMeasurable

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def controlledState (B : ℝ≥0 → Ω → ℝ) (α : ℝ≥0 → Ω → ℝ)
    (c x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x + B t ω - B 0 ω + stepDrift (fun r => α (Real.toNNReal r)) 0 t c ω

omit mΩ in
lemma controlledState_zero (B : ℝ≥0 → Ω → ℝ) (α : ℝ≥0 → Ω → ℝ)
    (c x : ℝ) (ω : Ω) : controlledState B α c x 0 ω = x := by
  simp [controlledState, stepDrift]

lemma controlledState_adapted {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) {α : ℝ≥0 → Ω → ℝ}
    (hα : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (c x : ℝ) (t : ℝ≥0) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) t]
      (controlledState B α c x t) := by
  have hBt := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) t).measurable
  have hB0 := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) 0).measurable.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono (show (0:ℝ≥0) ≤ t from bot_le)) le_rfl
  have hA := progressive_integral_measurable _ hα t (w := fun _ => c) measurable_const
  have hx : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) t]
      (fun _ : Ω => x) := measurable_const
  unfold controlledState stepDrift
  simp only [zero_add]
  exact ((hx.add hBt).sub hB0).add hA

lemma controlledState_integrable {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {α : ℝ≥0 → Ω → ℝ}
    (hm : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (c : ℝ≥0) (x : ℝ) (t : ℝ≥0) :
    Integrable (controlledState B α c x t) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hm' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    hm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  exact ((integrable_const x).add (hB.integrable_eval t) |>.sub (hB.integrable_eval 0)).add
    (stepDrift_integrable hm' (fun r ω => hb _ ω) 0 t c t.coe_nonneg c.coe_nonneg)

lemma stepDrift_add {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (c : ℝ) (s h : ℝ≥0) (ω : Ω) :
    stepDrift α 0 (s+h) c ω = stepDrift α 0 s c ω + stepDrift α s h c ω := by
  have h0 := (bounded_control_intervalIntegrable hm hb 0 s s.coe_nonneg ω).1.const_mul c
  have hs := (bounded_control_intervalIntegrable hm hb s h h.coe_nonneg ω).1.const_mul c
  simp only [zero_add] at h0
  simpa only [stepDrift, zero_add, NNReal.coe_add] using
    (intervalIntegral.integral_add_adjacent_intervals h0 hs).symm

lemma stepCost_add {α : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (c : ℝ) (s h : ℝ≥0) (ω : Ω) :
    stepCost α 0 (s+h) c ω = stepCost α 0 s c ω + stepCost α s h c ω := by
  have h0 := (bounded_control_intervalIntegrable hm hb 0 s s.coe_nonneg ω).2.const_mul c
  have hs := (bounded_control_intervalIntegrable hm hb s h h.coe_nonneg ω).2.const_mul c
  simp only [zero_add] at h0
  have he := intervalIntegral.integral_add_adjacent_intervals h0 hs
  simp only [stepCost, zero_add]
  rw [← he, mul_add]

lemma controlledState_increment {B : ℝ≥0 → Ω → ℝ} {α : ℝ≥0 → Ω → ℝ}
    (hm : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2))
    (hb : ∀ r ω, |α r ω| ≤ 1) (c x : ℝ) (s h : ℝ≥0) (ω : Ω) :
    controlledState B α c x (s+h) ω = controlledState B α c x s ω +
      (B (s+h) ω-B s ω) + stepDrift (fun r => α (Real.toNNReal r)) s h c ω := by
  have hm' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    hm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  simp only [controlledState]
  simp only [NNReal.coe_add]
  rw [stepDrift_add (α := fun r => α (Real.toNNReal r)) hm' (fun r ω => hb _ ω) c s h ω]
  ring

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto

def verificationError (c C₂ C₃ L h : ℝ) : ℝ :=
  C₃/6*(h*Real.sqrt h*normalThirdMoment) +
  C₂*c*h*(Real.sqrt h*normalFirstMoment+c*h) +
  L*h*(h+Real.sqrt h*normalFirstMoment+c*h)

lemma verificationError_limit (T c C₂ C₃ L : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)*verificationError c C₂ C₃ L (T/(n:ℝ)))
      atTop (𝓝 0) := by
  convert vanishing_mesh_error T
    (C₃/6*normalThirdMoment+C₂*c*normalFirstMoment+L*normalFirstMoment)
    (C₂*c^2+L*(1+c)) using 1
  funext n
  unfold verificationError
  ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem constant_interval_verification_upper (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {α : ℝ≥0 → Ω → ℝ}
    (hαm : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2))
    (hαp : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hαb : ∀ t ω, |α t ω| ≤ 1) (T c : ℝ≥0) (x : ℝ)
    {F D : ℝ → ℝ → ℝ} (hf : ∀ t, ContDiff ℝ 3 (F t))
    (C₁ C₂ C₃ Ct L : ℝ≥0) (hC₁ : ∀ t z, |deriv (F t) z| ≤ C₁)
    (hC₂ : ∀ t z, |deriv (deriv (F t)) z| ≤ C₂)
    (hC₃ : ∀ t z, |iteratedDeriv 3 (F t) z| ≤ C₃)
    (hDm : ∀ t, Measurable (D t)) (hCt : ∀ t z, |D t z| ≤ Ct)
    (hD : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z) (Set.Icc (0:ℝ) T) r)
    (hL : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ s ∈ Set.Icc (0:ℝ) T, ∀ z y,
      |D r z-D s y| ≤ (L:ℝ)*(|r-s|+|z-y|))
    (hPDE : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ z,
      D t z+(1/2:ℝ)*deriv (deriv (F t)) z+(c:ℝ)/2*(deriv (F t) z)^2 = 0) :
    (∫ ω, F T (controlledState B α c x T ω) ∂P) -
      (∫ ω, stepCost (fun r => α (Real.toNNReal r)) 0 T c ω ∂P) ≤ F 0 x := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let A (r : ℝ) := α (Real.toNNReal r)
  have hAm : Measurable (fun p : ℝ × Ω => A p.1 p.2) :=
    hαm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hAb : ∀ r ω, |A r ω| ≤ 1 := fun r ω => hαb _ ω
  let Q (t : ℝ≥0) := (∫ ω, F t (controlledState B α c x t ω) ∂P) -
    (∫ ω, stepCost A 0 t c ω ∂P)
  have hstep (s h : ℝ≥0) (hst : s+h ≤ T) :
      Q (s+h)-Q s ≤ verificationError c C₂ C₃ L h := by
    have hs : (s:ℝ) ∈ Set.Icc (0:ℝ) T :=
      ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr (le_trans (le_add_of_nonneg_right (show (0:ℝ≥0) ≤ h from bot_le)) hst)⟩
    have hsub : Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)) ⊆ Set.Icc (0:ℝ) T := by
      intro r hr
      constructor
      · exact le_trans s.coe_nonneg hr.1
      · exact hr.2.trans (by exact_mod_cast hst)
    have hh := expected_verification_step hB hm s h c
      (controlledState_adapted hm hαp c x s) (controlledState_integrable hB hαm hαb c x s) hAm hAb
      hf C₁ C₂ C₃ Ct L hC₁ hC₂ hC₃ (hDm s) (hCt s)
      (fun r hr z => (hD r (hsub hr) z).mono hsub)
      (fun r hr z y => hL r (hsub hr) s hs z y) (hPDE s hs)
    have hK : (∫ ω, stepCost A 0 ((s:ℝ)+(h:ℝ)) c ω ∂P) =
        (∫ ω, stepCost A 0 s c ω ∂P)+(∫ ω, stepCost A s h c ω ∂P) := by
      have he : stepCost A 0 ((s:ℝ)+(h:ℝ)) c = fun ω =>
          stepCost A 0 s c ω+stepCost A s h c ω := funext (stepCost_add hAm hAb c s h)
      rw [he, integral_add (stepCost_integrable hAm hAb 0 s c s.coe_nonneg c.coe_nonneg)
        (stepCost_integrable hAm hAb s h c h.coe_nonneg c.coe_nonneg)]
    have hF : (fun ω => F ((s:ℝ)+(h:ℝ))
        (controlledState B α c x s ω+(B (s+h) ω-B s ω)+stepDrift A s h c ω)) =
        (fun ω => F (s+h) (controlledState B α c x (s+h) ω)) := by
      funext ω
      rw [controlledState_increment hαm hαb c x s h ω]
    rw [hF] at hh
    dsimp only [Q]
    simp only [NNReal.coe_add]
    rw [hK]
    unfold verificationError
    linarith
  have hmesh : ∀ᶠ n : ℕ in atTop,
      Q T-Q 0 ≤ (n:ℝ)*verificationError c C₂ C₃ L ((T:ℝ)/(n:ℝ)) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (n:ℝ≥0) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    let h : ℝ≥0 := T/n
    have hend : (n:ℝ≥0)*h = T := by dsimp only [h]; field_simp
    have hh := finite_mesh_verification (fun k => Q ((k:ℝ≥0)*h)) (fun _ => 0) n
      (verificationError c C₂ C₃ L h) (by
        intro k hk
        have hbound : (k:ℝ≥0)*h+h ≤ T := by
          calc
            _ = ((k+1:ℕ):ℝ≥0)*h := by push_cast; ring
            _ ≤ (n:ℝ≥0)*h := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k+1 ≤ n)) (show (0:ℝ≥0) ≤ h from bot_le)
            _ = T := hend
        have he := hstep ((k:ℝ≥0)*h) h hbound
        have ht : ((k:ℝ≥0)*h+h) = ((k+1:ℕ):ℝ≥0)*h := by push_cast; ring
        simpa only [ht, sub_zero] using he)
    simpa only [hend, Nat.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero,
      h, NNReal.coe_div, NNReal.coe_natCast] using hh
  have hle : Q T-Q 0 ≤ 0 :=
    ge_of_tendsto (verificationError_limit T c C₂ C₃ L) hmesh
  have hQ0 : Q 0 = F 0 x := by
    simp [Q, controlledState_zero, stepCost]
  rw [hQ0] at hle
  exact sub_nonpos.mp hle

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
