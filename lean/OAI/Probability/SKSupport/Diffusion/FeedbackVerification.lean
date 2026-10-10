import Mathlib
import OAI.Probability.SKSupport.Diffusion.ExpectedFeedbackStep

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

lemma exists_feedback_verification (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (T c : ℝ≥0) (x : ℝ)
    {F D : ℝ → ℝ → ℝ} (hf : ∀ t, ContDiff ℝ 3 (F t))
    (C₂ C₃ Ct L : ℝ≥0) (hC₁ : ∀ t z, |deriv (F t) z| ≤ 1)
    (hC₂ : ∀ t z, |deriv (deriv (F t)) z| ≤ C₂)
    (hC₃ : ∀ t z, |iteratedDeriv 3 (F t) z| ≤ C₃)
    (hDm : ∀ t, Measurable (D t)) (hCt : ∀ t z, |D t z| ≤ Ct)
    (hD : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z) (Set.Icc (0:ℝ) T) r)
    (hL : ∀ r ∈ Set.Icc (0:ℝ) T, ∀ s ∈ Set.Icc (0:ℝ) T, ∀ z y,
      |D r z-D s y| ≤ (L:ℝ)*(|r-s|+|z-y|))
    (hPDE : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ z,
      D t z+(1/2:ℝ)*deriv (deriv (F t)) z+(c:ℝ)/2*(deriv (F t) z)^2 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α ∧
      (∀ t ω, |α t ω| ≤ 1) ∧
      F 0 x-ε ≤ (∫ ω, F T (controlledState B α c x T ω) ∂P) -
        (∫ ω, stepCost (fun r => α (Real.toNNReal r)) 0 T c ω ∂P) := by
  have hevent := (verificationError_limit T c C₂ C₃ L).eventually (gt_mem_nhds hε)
  obtain ⟨n, hn, he⟩ := ((eventually_ge_atTop (1:ℕ)).and hevent).exists
  have hn0 : (n:ℝ≥0) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  let h : ℝ≥0 := T/n
  have hend : (n:ℝ≥0)*h = T := by dsimp only [h]; field_simp
  have hend' : (n:ℝ)*(h:ℝ) = (T:ℝ) := by exact_mod_cast hend
  let u := fun t => deriv (F t)
  let α := elementaryControl h (fun k ω => u ((k:ℝ≥0)*h) (feedbackEuler B h c u x k ω)) n
  have hum : ∀ t, Measurable (u t) := fun t => (show ContDiff ℝ 2 (deriv (F t)) from (hf t).deriv').continuous.measurable
  have hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α :=
    elementaryControl_progressive _ h (fun k => (hum _).comp (feedbackEuler_adapted hm h c hum x k)) n
  have hab : ∀ t ω, |α t ω| ≤ 1 := elementaryControl_bound h (fun k ω => hC₁ _ _) n
  refine ⟨α, hap, hab, ?_⟩
  have hv := finite_feedback_verification hB hm h c x n hf C₂ C₃ Ct L hC₁ hC₂ hC₃ hDm hCt
    (by simpa only [hend'] using hD) (by simpa only [hend'] using hL)
    (by simpa only [hend'] using hPDE)
  change F 0 x-(n:ℝ)*verificationError c C₂ C₃ L h ≤
    (∫ ω, F ((n:ℝ)*(h:ℝ)) (controlledState B α c x ((n:ℝ≥0)*h) ω) ∂P) -
      (∫ ω, stepCost (fun r => α (Real.toNNReal r)) 0 ((n:ℝ)*(h:ℝ)) c ω ∂P) at hv
  rw [hend, hend'] at hv
  have herr : (n:ℝ)*verificationError c C₂ C₃ L h < ε := by
    simpa only [h, NNReal.coe_div, NNReal.coe_natCast] using he
  linarith

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
