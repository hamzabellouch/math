import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityHybridSieve

namespace OAI

/-! # Point sampling from the energy of a differentiable complex function -/

namespace Ostmann

open MeasureTheory Set
open scoped ComplexConjugate

 theorem density_energy_derivative_bound {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    ‖deriv (fun t => ‖f t‖ ^ 2) x‖ ≤ ‖f x‖ ^ 2 + ‖f'‖ ^ 2 := by
  rw [hf.norm_sq.deriv]
  have hi := norm_inner_le_norm (𝕜 := ℝ) (f x) f'
  have hnorm : ‖(2 : ℝ) * inner ℝ (f x) f'‖ ≤ 2 * (‖f x‖ * ‖f'‖) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hi (by norm_num)
  exact hnorm.trans (by nlinarith [sq_nonneg (‖f x‖ - ‖f'‖)])

 theorem density_energy_oscillation (f g : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (a b t u : ℝ) (ht : t ∈ Icc a b) (hu : u ∈ Icc a b) :
    ‖f t‖ ^ 2 ≤ ‖f u‖ ^ 2 + ∫ x in a..b, (‖f x‖ ^ 2 + ‖g x‖ ^ 2) := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hcE : Continuous (fun x => ‖f x‖ ^ 2) := hcont.norm.pow 2
  have hcB : Continuous (fun x => ‖f x‖ ^ 2 + ‖g x‖ ^ 2) :=
    (hcont.norm.pow 2).add (hg.norm.pow 2)
  have hdE : Differentiable ℝ (fun x => ‖f x‖ ^ 2) := fun x => (hf x).norm_sq.differentiableAt
  have hbound : ∀ᵐ x : ℝ, ‖deriv (fun t => ‖f t‖ ^ 2) x‖ ≤ ‖f x‖ ^ 2 + ‖g x‖ ^ 2 :=
    Filter.Eventually.of_forall (fun x => density_energy_derivative_bound (hf x))
  have hab : a ≤ b := ht.1.trans ht.2
  have hbnon : ∀ᵐ x : ℝ, 0 ≤ ‖f x‖ ^ 2 + ‖g x‖ ^ 2 :=
    Filter.Eventually.of_forall (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hstep (v w : ℝ) (hv : v ∈ Icc a b) (hw : w ∈ Icc a b) (hvw : v ≤ w) :
      ‖‖f w‖ ^ 2 - ‖f v‖ ^ 2‖ ≤ ∫ x in a..b, (‖f x‖ ^ 2 + ‖g x‖ ^ 2) := by
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le hvw hcE.continuousOn
      hdE.differentiableOn (hbound.mono (fun _ hx _ => hx)) (hcB.intervalIntegrable v w)
    have hm := intervalIntegral.integral_mono_interval hv.1 hvw hw.2 (ae_restrict_of_ae hbnon)
      (hcB.intervalIntegrable a b)
    exact h.trans hm
  have hdiff : ‖‖f t‖ ^ 2 - ‖f u‖ ^ 2‖ ≤
      ∫ x in a..b, (‖f x‖ ^ 2 + ‖g x‖ ^ 2) := by
    rcases le_total u t with h | h
    · exact hstep u t hu ht h
    · simpa only [norm_sub_rev] using hstep t u ht hu h
  have hl := (le_abs_self (‖f t‖ ^ 2 - ‖f u‖ ^ 2)).trans
    (by simpa only [Real.norm_eq_abs] using hdiff)
  linarith

 theorem density_unit_interval_sample (f g : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) (t : ℝ) :
    ‖f t‖ ^ 2 ≤ 2 * (∫ x in t - 1 / 2..t + 1 / 2, ‖f x‖ ^ 2) +
      ∫ x in t - 1 / 2..t + 1 / 2, ‖g x‖ ^ 2 := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hab : t - 1 / 2 ≤ t + 1 / 2 := by linarith
  have hpoint (u : ℝ) (hu : u ∈ Icc (t - 1 / 2) (t + 1 / 2)) :=
    density_energy_oscillation f g hf hg (t - 1 / 2) (t + 1 / 2) t u
      ⟨by linarith, by linarith⟩ hu
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const
    (((hcont.norm.pow 2).intervalIntegrable (t - 1 / 2) (t + 1 / 2)).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add,
    intervalIntegral.integral_const, intervalIntegral.integral_add] at hi
  · simp only [show t + 1 / 2 - (t - 1 / 2) = (1 : ℝ) by ring, smul_eq_mul,
      one_mul] at hi
    change ‖f t‖ ^ 2 ≤ (∫ x in t - 1 / 2..t + 1 / 2, ‖f x‖ ^ 2) +
      ((∫ x in t - 1 / 2..t + 1 / 2, ‖f x‖ ^ 2) +
       ∫ x in t - 1 / 2..t + 1 / 2, ‖g x‖ ^ 2) at hi
    linarith
  · exact (hcont.norm.pow 2).intervalIntegrable _ _
  · exact (hg.norm.pow 2).intervalIntegrable _ _
  · exact (hcont.norm.pow 2).intervalIntegrable _ _
  · exact intervalIntegrable_const

end Ostmann

end OAI
