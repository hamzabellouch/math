import OAI.NumberTheory.Ostmann.QuadraticSieveMellinDecay

namespace OAI

namespace Ostmann
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap

theorem schwartz_mellin_vertical_decay_real (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖mellin (ρ : ℝ → ℂ) (σ + t * Complex.I)‖ ≤ C * (1 + |t|) ^ (-A) := by
  obtain ⟨C, hC, hb⟩ := schwartz_mellin_vertical_decay ρ σ hσ ⌈A⌉₊
  refine ⟨C, hC, ?_⟩
  intro t
  apply (hb t).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  rw [← Real.rpow_intCast]
  push_cast
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (neg_le_neg (Nat.le_ceil A))

theorem schwartz_mellin_vertical_continuous (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t : ℝ => mellin (ρ : ℝ → ℂ) (σ + t * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : ContinuousAt (fun u : ℝ => (σ : ℂ) + u * Complex.I) t := by fun_prop
  exact (schwartz_mellin_differentiableAt ρ (s := σ + t * Complex.I)
    (by simpa using hσ)).continuousAt.comp (f := fun u : ℝ => (σ : ℂ) + u * Complex.I) hc

theorem schwartz_mellin_vertical_integrable (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (mellin (ρ : ℝ → ℂ)) σ := by
  obtain ⟨C, hC, hb⟩ := schwartz_mellin_vertical_decay_real ρ σ hσ 2
  have hk : Integrable (fun t : ℝ => C * (1 + |t|) ^ (-(2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul C
  exact hk.mono' (schwartz_mellin_vertical_continuous ρ σ hσ).aestronglyMeasurable
    (ae_of_all _ hb)

theorem schwartz_mellin_inversion (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    {x : ℝ} (hx : 0 < x) : mellinInv σ (mellin (ρ : ℝ → ℂ)) x = ρ x := by
  exact mellinInv_mellin_eq σ (ρ : ℝ → ℂ) hx
    (schwartz_mellin_convergent ρ (by simpa using hσ))
    (schwartz_mellin_vertical_integrable ρ σ hσ) ρ.continuous.continuousAt

theorem schwartz_mellin_inversion_integral (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℝ) •
      (∫ t : ℝ, (x : ℂ) ^ (-(σ + t * Complex.I)) *
        mellin (ρ : ℝ → ℂ) (σ + t * Complex.I)) = ρ x := by
  simpa only [mellinInv, smul_eq_mul] using schwartz_mellin_inversion ρ σ hσ hx

noncomputable def reflectedSchwartz (ρ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) ρ

@[simp] theorem reflectedSchwartz_apply (ρ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    reflectedSchwartz ρ x = ρ (-x) := rfl

theorem schwartz_mellin_neg_convergent (ρ : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => ρ (-x)) s :=
  schwartz_mellin_convergent (reflectedSchwartz ρ) hs

theorem schwartz_mellin_neg_differentiableAt (ρ : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (fun x : ℝ => ρ (-x))) s :=
  schwartz_mellin_differentiableAt (reflectedSchwartz ρ) hs

theorem schwartz_mellin_neg_vertical_decay (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖mellin (fun x : ℝ => ρ (-x)) (σ + t * Complex.I)‖ ≤ C * (1 + |t|) ^ (-A) :=
  schwartz_mellin_vertical_decay_real (reflectedSchwartz ρ) σ hσ A

theorem schwartz_mellin_neg_inversion (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ)
    {x : ℝ} (hx : 0 < x) : mellinInv σ (mellin (fun y : ℝ => ρ (-y))) x = ρ (-x) :=
  schwartz_mellin_inversion (reflectedSchwartz ρ) σ hσ hx

end Ostmann

end OAI
