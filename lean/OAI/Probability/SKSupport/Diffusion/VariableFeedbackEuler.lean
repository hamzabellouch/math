import Mathlib
import OAI.Probability.SKSupport.Diffusion.ExpectedFeedbackStep
import OAI.Probability.SKSupport.Control.ControlledGrid

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

def variableFeedbackEuler (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (c : ℕ → ℝ≥0)
    (u : ℕ → ℝ → ℝ) (x : ℝ) : ℕ → Ω → ℝ
  | 0, _ => x
  | k+1, ω => variableFeedbackEuler B h c u x k ω +
      (B (((k+1:ℕ):ℝ≥0)*h) ω-B ((k:ℝ≥0)*h) ω)+
      (c k:ℝ)*(h:ℝ)*u k (variableFeedbackEuler B h c u x k ω)

lemma variableFeedbackEuler_adapted (hm : ∀ t, Measurable (B t))
    (h : ℝ≥0) (c : ℕ → ℝ≥0) {u : ℕ → ℝ → ℝ} (hum : ∀ k, Measurable (u k))
    (x : ℝ) (n : ℕ) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) ((n:ℝ≥0)*h)]
      (variableFeedbackEuler B h c u x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n IH =>
    have hle : (n:ℝ≥0)*h ≤ ((n+1:ℕ):ℝ≥0)*h := by gcongr; exact_mod_cast Nat.le_succ n
    have hYm := IH.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBs := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) ((n:ℝ≥0)*h)).measurable.mono
      ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBt := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (((n+1:ℕ):ℝ≥0)*h)).measurable
    exact (hYm.add (hBt.sub hBs)).add (((hum _).comp hYm).const_mul ((c n:ℝ)*(h:ℝ)))

omit mΩ in
lemma variableFeedback_controlledGrid (h : ℝ≥0) (c : ℕ → ℝ≥0)
    (u : ℕ → ℝ → ℝ) (x : ℝ) (n k : ℕ) (hk : k ≤ n) (ω : Ω) :
    let a := fun j ω => u j (variableFeedbackEuler B h c u x j ω)
    controlledGrid B (elementaryControl h a n) h c x k ω =
      variableFeedbackEuler B h c u x k ω := by
  dsimp only
  induction k with
  | zero => rfl
  | succ k IH =>
    have hk' : k < n := by omega
    have he := elementaryControl_integral_on_step h
      (fun j ω => u j (variableFeedbackEuler B h c u x j ω)) n k hk'
      (fun z => (c k:ℝ)*z) ω
    change stepDrift (fun r => elementaryControl h
      (fun j ω => u j (variableFeedbackEuler B h c u x j ω)) n (Real.toNNReal r))
      ((k:ℝ≥0)*h) h (c k) ω = _ at he
    simp only [controlledGrid, he, IH hk'.le, variableFeedbackEuler]
    ring

lemma variable_grid_verification_lower (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (h : ℝ≥0) (c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ)
    {F D : ℕ → ℝ → ℝ → ℝ} (C₂ C₃ Ct L : ℕ → ℝ≥0)
    (hf : ∀ k t, ContDiff ℝ 3 (F k t))
    (hC₁ : ∀ k t z, |deriv (F k t) z| ≤ 1)
    (hC₂ : ∀ k < n, ∀ t z, |deriv (deriv (F k t)) z| ≤ C₂ k)
    (hC₃ : ∀ k < n, ∀ t z, |iteratedDeriv 3 (F k t) z| ≤ C₃ k)
    (hDm : ∀ k < n, Measurable (D k ((k:ℝ≥0)*h)))
    (hCt : ∀ k < n, ∀ z, |D k ((k:ℝ≥0)*h) z| ≤ Ct k)
    (hD : ∀ k < n, ∀ r ∈ Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)), ∀ z,
      HasDerivWithinAt (fun t => F k t z) (D k r z)
        (Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ))) r)
    (hL : ∀ k < n, ∀ r ∈ Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)), ∀ z y,
      |D k r z-D k ((k:ℝ≥0)*h) y| ≤ (L k:ℝ)*(|r-(k:ℝ)*(h:ℝ)|+|z-y|))
    (hPDE : ∀ k < n, ∀ z, D k ((k:ℝ≥0)*h) z+
      (1/2:ℝ)*deriv (deriv (F k ((k:ℝ≥0)*h))) z+
        (c k:ℝ)/2*(deriv (F k ((k:ℝ≥0)*h)) z)^2 = 0)
    (hseam : ∀ k < n, F k (((k+1:ℕ):ℝ)*(h:ℝ)) = F (k+1) (((k+1:ℕ):ℝ)*(h:ℝ)))
    {ε : ℝ} (hε : ∀ k < n, verificationError (c k) (C₂ k) (C₃ k) (L k) h ≤ ε) :
    ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α ∧
      (∀ t ω, |α t ω| ≤ 1) ∧
      F 0 0 x-(n:ℝ)*ε ≤
        (∫ ω, F n ((n:ℝ)*(h:ℝ)) (controlledGrid B α h c x n ω) ∂P)-
          (∑ k ∈ Finset.range n, ∫ ω, stepCost (fun r => α (Real.toNNReal r))
            ((k:ℝ≥0)*h) h (c k) ω ∂P) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let u (k : ℕ) := deriv (F k ((k:ℝ≥0)*h))
  let a (k : ℕ) (ω : Ω) := u k (variableFeedbackEuler B h c u x k ω)
  let α := elementaryControl h a n
  have hum : ∀ k, Measurable (u k) := fun k =>
    (show ContDiff ℝ 2 (u k) from (hf k _).deriv').continuous.measurable
  have hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α :=
    elementaryControl_progressive _ h (fun k => (hum k).comp
      (variableFeedbackEuler_adapted hm h c hum x k)) n
  have hab : ∀ t ω, |α t ω| ≤ 1 := elementaryControl_bound h (fun k ω => hC₁ _ _ _) n
  refine ⟨α,hap,hab,?_⟩
  have ham := progressive_joint_measurable _ hap
  have hgrid (k : ℕ) (hk : k ≤ n) (ω : Ω) :
      controlledGrid B α h c x k ω = variableFeedbackEuler B h c u x k ω :=
    variableFeedback_controlledGrid h c u x n k hk ω
  let Q (k : ℕ) := ∫ ω, F k ((k:ℝ)*(h:ℝ)) (controlledGrid B α h c x k ω) ∂P
  let K (k : ℕ) := ∫ ω, stepCost (fun r => α (Real.toNNReal r)) ((k:ℝ≥0)*h) h (c k) ω ∂P
  have hstep : ∀ k < n, -Q (k+1)-(-Q k)-(-K k) ≤ ε := by
    intro k hk
    have ht : (k:ℝ≥0)*h+h = ((k+1:ℕ):ℝ≥0)*h := by push_cast; ring
    have ht' : (↑((k:ℝ≥0)*h):ℝ)+(h:ℝ) = (((k:ℝ)+1)*(h:ℝ)) := by push_cast; ring
    have hg := expected_feedback_step hB hm ((k:ℝ≥0)*h) h (c k)
      (controlledGrid_adapted hm hap hab h c x k) (controlledGrid_integrable hB ham hab h c x k)
      (hf k) (C₂ k) (C₃ k) (Ct k) (L k) (hC₁ k) (hC₂ k hk) (hC₃ k hk) (hDm k hk) (hCt k hk)
      (by simpa only [NNReal.coe_mul, NNReal.coe_natCast, add_mul, one_mul] using hD k hk)
      (by simpa only [NNReal.coe_mul, NNReal.coe_natCast, add_mul, one_mul] using hL k hk)
      (hPDE k hk)
    have he : (fun ω => F k ((↑((k:ℝ≥0)*h):ℝ)+(h:ℝ))
        (controlledGrid B α h c x k ω+(B ((k:ℝ≥0)*h+h) ω-B ((k:ℝ≥0)*h) ω)+
          (c k:ℝ)*(h:ℝ)*deriv (F k ((k:ℝ≥0)*h)) (controlledGrid B α h c x k ω))) =
        fun ω => F (k+1) (((k+1:ℕ):ℝ)*(h:ℝ)) (controlledGrid B α h c x (k+1) ω) := by
      funext ω
      rw [ht, ht']
      simp only [← Nat.cast_add_one, hseam k hk]
      rw [hgrid k hk.le, hgrid (k+1) (by omega)]
      rfl
    simp only [NNReal.coe_mul, NNReal.coe_natCast] at hg he
    rw [he] at hg
    have hK : K k = (c k:ℝ)*(h:ℝ)/2*
        (∫ ω, (deriv (F k ((k:ℝ≥0)*h)) (controlledGrid B α h c x k ω))^2 ∂P) := by
      dsimp only [K]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      have hh := elementary_stepCost h (c k) a n k hk ω
      change stepCost (fun r => α (Real.toNNReal r)) ((k:ℝ≥0)*h) h (c k) ω =
        (c k:ℝ)*(h:ℝ)/2*(a k ω)^2 at hh
      rw [hh]
      dsimp only [a, u]
      rw [hgrid k hk.le]
    have hg' : |Q (k+1)-Q k-K k| ≤ ε := by
      rw [hK]
      exact hg.trans (hε k hk)
    linarith [(abs_le.mp hg').1]
  have hh := finite_mesh_verification (fun k => -Q k) (fun k => -K k) n ε hstep
  have hz : Q 0 = F 0 0 x := by simp [Q, controlledGrid]
  rw [hz, Finset.sum_neg_distrib] at hh
  change F 0 0 x-(n:ℝ)*ε ≤ Q n-∑ k ∈ Finset.range n, K k
  linarith

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
