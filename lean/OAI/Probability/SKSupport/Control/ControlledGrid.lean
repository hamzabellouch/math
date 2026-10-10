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

lemma progressive_stepDrift_measurable (ℱ : Filtration ℝ≥0 mΩ)
    {α : ℝ≥0 → Ω → ℝ} (hap : IsProgressive ℱ α) (hab : ∀ t ω, |α t ω| ≤ 1)
    (s h : ℝ≥0) (c : ℝ) :
    Measurable[ℱ (s+h)] (stepDrift (fun r => α (Real.toNNReal r)) s h c) := by
  have ham := progressive_joint_measurable ℱ hap
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have h₁ := progressive_integral_measurable ℱ hap (s+h) (w := fun _ => c) measurable_const
  have h₂ := (progressive_integral_measurable ℱ hap s (w := fun _ => c) measurable_const).mono
    (ℱ.mono (show s ≤ s+h from le_add_of_nonneg_right (show (0:ℝ≥0) ≤ h from zero_le))) le_rfl
  have he : stepDrift (fun r => α (Real.toNNReal r)) s h c = fun ω =>
      (∫ r in (0:ℝ)..((s+h:ℝ≥0):ℝ), c*α (Real.toNNReal r) ω)-
      (∫ r in (0:ℝ)..(s:ℝ), c*α (Real.toNNReal r) ω) := by
    funext ω
    have hh := stepDrift_add (α := fun r => α (Real.toNNReal r)) ham' (fun r ω => hab _ ω) c s h ω
    simpa only [stepDrift, zero_add, NNReal.coe_add] using (eq_sub_of_add_eq' hh.symm)
  rw [he]
  exact h₁.sub h₂

def controlledGrid (B : ℝ≥0 → Ω → ℝ) (α : ℝ≥0 → Ω → ℝ) (h : ℝ≥0)
    (c : ℕ → ℝ≥0) (x : ℝ) : ℕ → Ω → ℝ
  | 0, _ => x
  | n+1, ω => controlledGrid B α h c x n ω+
      (B (((n+1:ℕ):ℝ≥0)*h) ω-B ((n:ℝ≥0)*h) ω)+
      stepDrift (fun r => α (Real.toNNReal r)) ((n:ℝ≥0)*h) h (c n) ω

lemma controlledGrid_adapted (hm : ∀ t, Measurable (B t))
    {α : ℝ≥0 → Ω → ℝ}
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ω, |α t ω| ≤ 1) (h : ℝ≥0) (c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) ((n:ℝ≥0)*h)]
      (controlledGrid B α h c x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n IH =>
    have hle : (n:ℝ≥0)*h ≤ ((n+1:ℕ):ℝ≥0)*h := by gcongr; exact_mod_cast Nat.le_succ n
    have hYm := IH.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBs := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) ((n:ℝ≥0)*h)).measurable.mono
      ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hle) le_rfl
    have hBt := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) (((n+1:ℕ):ℝ≥0)*h)).measurable
    have ht : (n:ℝ≥0)*h+h = ((n+1:ℕ):ℝ≥0)*h := by push_cast; ring
    have hAm := progressive_stepDrift_measurable _ hap hab ((n:ℝ≥0)*h) h (c n)
    rw [ht] at hAm
    exact (hYm.add (hBt.sub hBs)).add hAm

lemma controlledGrid_integrable (hB : IsPreBrownianReal B P)
    {α : ℝ≥0 → Ω → ℝ} (ham : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2))
    (hab : ∀ t ω, |α t ω| ≤ 1) (h : ℝ≥0) (c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ) :
    Integrable (controlledGrid B α h c x n) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  induction n with
  | zero => exact integrable_const x
  | succ n IH =>
    exact (IH.add ((hB.integrable_eval _).sub (hB.integrable_eval _))).add
      (stepDrift_integrable ham' (fun r ω => hab _ ω) ((n:ℝ≥0)*h) h (c n) h.coe_nonneg (c n).coe_nonneg)

lemma variable_grid_verification_upper (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {α : ℝ≥0 → Ω → ℝ}
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ω, |α t ω| ≤ 1) (h : ℝ≥0) (c : ℕ → ℝ≥0) (x : ℝ) (n : ℕ)
    {F D : ℕ → ℝ → ℝ → ℝ} (C₂ C₃ Ct L : ℕ → ℝ≥0)
    (hf : ∀ k < n, ∀ t, ContDiff ℝ 3 (F k t))
    (hC₁ : ∀ k < n, ∀ t z, |deriv (F k t) z| ≤ 1)
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
    (∫ ω, F n ((n:ℝ)*(h:ℝ)) (controlledGrid B α h c x n ω) ∂P)-F 0 0 x-
      (∑ k ∈ Finset.range n, ∫ ω, stepCost (fun r => α (Real.toNNReal r))
        ((k:ℝ≥0)*h) h (c k) ω ∂P) ≤ (n:ℝ)*ε := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have ham := progressive_joint_measurable _ hap
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  let Q (k : ℕ) := ∫ ω, F k ((k:ℝ)*(h:ℝ)) (controlledGrid B α h c x k ω) ∂P
  let K (k : ℕ) := ∫ ω, stepCost (fun r => α (Real.toNNReal r)) ((k:ℝ≥0)*h) h (c k) ω ∂P
  have hstep : ∀ k < n, Q (k+1)-Q k-K k ≤ ε := by
    intro k hk
    have ht : (k:ℝ≥0)*h+h = ((k+1:ℕ):ℝ≥0)*h := by push_cast; ring
    have ht' : (↑((k:ℝ≥0)*h):ℝ)+(h:ℝ) = (((k:ℝ)+1)*(h:ℝ)) := by push_cast; ring
    have hu := expected_verification_step hB hm ((k:ℝ≥0)*h) h (c k)
      (controlledGrid_adapted hm hap hab h c x k) (controlledGrid_integrable hB ham hab h c x k)
      (α := fun r => α (Real.toNNReal r)) ham' (fun r ω => hab _ ω) (hf k hk) 1 (C₂ k) (C₃ k) (Ct k) (L k)
      (hC₁ k hk) (hC₂ k hk) (hC₃ k hk) (hDm k hk) (hCt k hk)
      (by simpa only [NNReal.coe_mul, NNReal.coe_natCast, add_mul, one_mul] using hD k hk)
      (by simpa only [NNReal.coe_mul, NNReal.coe_natCast, add_mul, one_mul] using hL k hk)
      (hPDE k hk)
    have he : (fun ω => F k ((↑((k:ℝ≥0)*h):ℝ)+(h:ℝ))
        (controlledGrid B α h c x k ω+(B ((k:ℝ≥0)*h+h) ω-B ((k:ℝ≥0)*h) ω)+
          stepDrift (fun r => α (Real.toNNReal r)) ((k:ℝ≥0)*h) h (c k) ω)) =
        fun ω => F (k+1) (((k+1:ℕ):ℝ)*(h:ℝ)) (controlledGrid B α h c x (k+1) ω) := by
      funext ω
      rw [ht, ht']
      simp only [← Nat.cast_add_one, hseam k hk, controlledGrid]
    simp only [NNReal.coe_mul, NNReal.coe_natCast] at hu he
    rw [he] at hu
    exact (show Q (k+1)-Q k-K k ≤ verificationError (c k) (C₂ k) (C₃ k) (L k) h from hu).trans (hε k hk)
  have hh := finite_mesh_verification Q K n ε hstep
  have hz : Q 0 = F 0 0 x := by simp [Q, controlledGrid]
  rw [hz] at hh
  exact hh

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
