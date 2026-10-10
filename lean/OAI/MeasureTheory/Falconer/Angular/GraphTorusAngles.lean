import OAI.MeasureTheory.Falconer.Angular.StationaryArcLength
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem continuous_interval_integral_swap {f : ℝ → ℝ → ℂ}
    (hf : Continuous (Function.uncurry f)) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, f x y) =
      ∫ y in c..d, ∫ x in a..b, f x y := by
  have hi : IntegrableOn (Function.uncurry f) ((Icc a b) ×ˢ (Icc c d)) volume :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi' : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simpa only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
    using integral_integral_swap hi'

theorem periodic_half_difference_integral {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    (∫ u in (-Real.pi)..Real.pi, f u) =
      (2 : ℝ) • ∫ α in (-Real.pi/2)..(Real.pi/2), f (θ-2*α) := by
  rw [intervalIntegral.smul_integral_comp_sub_mul]
  have h := hp.intervalIntegral_add_eq (-Real.pi) (θ-Real.pi)
  convert h using 1 <;> congr 1 <;> ring

theorem periodic_mean_angle_integral {F : ℝ → ℝ → ℂ}
    (hp : ∀ u v, F (u+2*Real.pi) (v+2*Real.pi) = F u v) (α : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, F θ (θ-2*α)) =
      ∫ φ in (-Real.pi)..Real.pi, F (φ+α) (φ-α) := by
  let g : ℝ → ℂ := fun θ => F θ (θ-2*α)
  have hg : Function.Periodic g (2*Real.pi) := by
    intro θ
    dsimp [g]
    rw [show θ+2*Real.pi-2*α = (θ-2*α)+2*Real.pi by ring]
    exact hp θ (θ-2*α)
  have he : (fun φ => F (φ+α) (φ-α)) = fun φ => g (φ+α) := by
    funext φ
    dsimp [g]
    congr 1
    ring
  rw [he, intervalIntegral.integral_comp_add_right]
  have h := hg.intervalIntegral_add_eq (-Real.pi) (-Real.pi+α)
  convert h using 1 <;> congr 1 <;> ring

theorem graph_torus_mean_half_difference {F : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F))
    (h₁ : ∀ v, Function.Periodic (fun u => F u v) (2*Real.pi))
    (h₂ : ∀ u, Function.Periodic (F u) (2*Real.pi)) :
    (∫ θ₁ in (-Real.pi)..Real.pi, ∫ θ₂ in (-Real.pi)..Real.pi, F θ₁ θ₂) =
      (2 : ℝ) • ∫ α in (-Real.pi/2)..(Real.pi/2),
        ∫ φ in (-Real.pi)..Real.pi, F (φ+α) (φ-α) := by
  have he : (fun θ₁ => ∫ θ₂ in (-Real.pi)..Real.pi, F θ₁ θ₂) =
      fun θ₁ => (2 : ℝ) • ∫ α in (-Real.pi/2)..(Real.pi/2), F θ₁ (θ₁-2*α) := by
    funext θ₁
    exact periodic_half_difference_integral (h₂ θ₁) θ₁
  rw [he]
  rw [intervalIntegral.integral_smul]
  have hc : Continuous (fun p : ℝ × ℝ => F p.1 (p.1-2*p.2)) :=
    hF.comp (continuous_fst.prodMk (continuous_fst.sub (continuous_const.mul continuous_snd)))
  rw [continuous_interval_integral_swap (f := fun θ α => F θ (θ-2*α)) hc (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])]
  congr 1
  apply intervalIntegral.integral_congr
  intro α hα
  exact periodic_mean_angle_integral (fun u v => (h₁ (v+2*Real.pi) u).trans (h₂ u v)) α

end PlanarFalconer

end OAI
