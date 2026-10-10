import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2ComplexMultiplier
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Dominated pointwise convergence for the L² coordinates of the harmonic form. -/

open MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralL2_dominated_tendsto (μ : Measure ℝ) (v : ℕ → Lp ℂ 2 μ)
    (u : Lp ℂ 2 μ) (g : ℝ → ℝ) (hg : Integrable g μ)
    (hb : ∀ n, ∀ᵐ r ∂μ, ‖v n r-u r‖^2 ≤ g r)
    (hp : ∀ᵐ r ∂μ, Tendsto (fun n => v n r) atTop (𝓝 (u r))) :
    Tendsto v atTop (𝓝 u) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun r => ‖v n r-u r‖^2) μ :=
    ((Lp.aestronglyMeasurable (v n)).sub (Lp.aestronglyMeasurable u)).norm.pow 2
  have hp' : ∀ᵐ r ∂μ, Tendsto (fun n => ‖v n r-u r‖^2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hp] with r hr
    simpa only [sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (hr.sub_const (u r)).norm.pow 2
  have hb' (n : ℕ) : ∀ᵐ r ∂μ, ‖‖v n r-u r‖^2‖ ≤ g r := by
    filter_upwards [hb n] with r hr
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖v n r-u r‖)] using hr
  have hi : Tendsto (fun n => ∫ r, ‖v n r-u r‖^2 ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence g hm hg hb' hp'
  have he (n : ℕ) : ‖v n-u‖^2=∫ r, ‖v n r-u r‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq]
    change (∫ r, inner ℝ ((v n-u) r) ((v n-u) r) ∂μ)=_
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (v n) u] with r hr
    rw [hr,Pi.sub_apply,real_inner_self_eq_norm_sq]
  have hn : Tendsto (fun n => ‖v n-u‖^2) atTop (𝓝 0) := by
    simpa only [← he] using hi
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hroot

end DefocusingNLS

end OAI
