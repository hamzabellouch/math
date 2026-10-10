import OAI.GroupTheory.Thompson.AnalyticModel
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace OAI

/-!
# Uniform estimates in the concrete Hilbert space

The restricted Lebesgue measure has mass one. Consequently, an almost-everywhere
uniform bound on a representative gives the same bound on its `L²` norm.
The derivative criterion below turns a quadratic norm remainder into a genuine
derivative in any real normed space, including this Hilbert space.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic

open MeasureTheory Set Filter
open scoped Topology Asymptotics ENNReal

@[simp] theorem intervalMeasure_univ : intervalMeasure univ = 1 := by
  simp [intervalMeasure, Real.volume_Icc]

/-- A uniform bound on an almost-everywhere representative bounds the Hilbert norm. -/
theorem norm_le_of_ae_bound (f : Hilbert) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂intervalMeasure, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [Lp.norm_def]
  have h : eLpNorm f 2 intervalMeasure ≤ ENNReal.ofReal C := by
    simpa only [intervalMeasure_univ, ENNReal.one_rpow, one_mul] using
      (eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) (Lp.aestronglyMeasurable f) hbound)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal hC)

/-- The same estimate for an explicitly supplied square-integrable function. -/
theorem norm_toLp_le {f : ℝ → Plane} (hf : MemLp f 2 intervalMeasure)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂intervalMeasure, ‖f x‖ ≤ C) :
    ‖hf.toLp f‖ ≤ C := by
  apply norm_le_of_ae_bound (hf.toLp f) hC
  filter_upwards [hf.coeFn_toLp, hbound] with x hx hxbound
  simpa only [hx] using hxbound

/-- A quadratic norm remainder implies differentiability, without any pointwise
choice of representatives in the codomain. -/
theorem hasDerivAt_of_quadratic_remainder
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {x C : ℝ}
    (hrem : ∀ᶠ h in 𝓝 (0 : ℝ),
      ‖f (x + h) - f x - h • f'‖ ≤ C * |h| ^ 2) :
    HasDerivAt f f' x := by
  apply hasDerivAt_iff_isLittleO_nhds_zero.mpr
  have hO :
      (fun h : ℝ => f (x + h) - f x - h • f') =O[𝓝 0]
        (fun h : ℝ => h ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    simpa only [norm_pow, Real.norm_eq_abs] using hrem
  exact hO.trans_isLittleO
    (Asymptotics.isLittleO_pow_id (n := 2) (by decide))

end ThompsonNonamenability.Analytic

end

end OAI
