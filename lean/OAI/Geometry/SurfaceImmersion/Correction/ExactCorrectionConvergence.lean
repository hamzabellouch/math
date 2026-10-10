import OAI.Geometry.SurfaceImmersion.Correction.CorrectionScales
import OAI.Geometry.SurfaceImmersion.Correction.ExactCorrectionLimit

namespace OAI

/-!
# Convergence after the derivative orders have been scheduled

This combines the particular scales and increasing derivative budgets of
the exact-correction iteration with the smooth-series limit argument.
Constructing the increments with these bounds remains a separate step.
-/

noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

open Filter
open scoped Topology ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- Increasing finite derivative budgets suffice: every fixed derivative
order eventually has a summable bound. -/
theorem eventual_increment_bound {U : ℕ → E → V} {t ρ : ℝ} {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop)
    (hU : ∀ n m, m ≤ k n / 2 → ∀ x,
      ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ * correctionScale t n) (m : ℕ) :
    ∀ᶠ n in atTop, ∀ x,
      ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ * correctionScale t n := by
  filter_upwards [hk.eventually (eventually_ge_atTop (2 * m))] with n hn
  exact hU n m (by omega)

/-- Quantitative conclusion of the last part of `exact-correction.tex`:
the superlinear scale decay, increasing derivative orders, and bounded
normalized defect imply a smooth exact isometric limit. -/
theorem exact_limit_of_increment_bounds
    {F : E → V} {U : ℕ → E → V} {t ρ C : ℝ} {k : ℕ → ℕ}
    (ht : 0 ≤ t) (htsmall : t ≤ 1 / 32) (hC : 0 ≤ C)
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hk : Tendsto k atTop atTop) (hkpos : ∀ n, 1 ≤ k n)
    (hinc : ∀ n m, m ≤ k n / 2 → ∀ x,
      ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ * correctionScale t n)
    (g : E → E → E → ℝ)
    (herror : ∀ n x v w,
      |inner ℝ (fderiv ℝ (partialMap F U n) x v)
        (fderiv ℝ (partialMap F U n) x w) - g x v w| ≤
          C * correctionScale t n ^ (2 * k n) * ‖v‖ * ‖w‖) :
    ContDiff ℝ ∞ (limitMap F U) ∧
      ∀ x v w, inner ℝ (fderiv ℝ (limitMap F U) x v)
        (fderiv ℝ (limitMap F U) x w) = g x v w := by
  have hscale := (correctionScale_summable ht htsmall).1
  have hsum : Summable (fun n => ρ * correctionScale t n) := hscale.mul_left ρ
  have hb := eventual_increment_bound hk hinc
  refine ⟨smooth_limitMap hF hU hsum hb, ?_⟩
  apply limitMap_metric_of_error_bound hF hU hsum hb g
    (ε := fun n => C * correctionScale t n)
  · simpa using hscale.tendsto_atTop_zero.const_mul C
  · intro n x v w
    have hsnonneg := correctionScale_nonneg ht n
    have hsone : correctionScale t n ≤ 1 := by
      have hg := correctionScale_le_geometric ht htsmall n
      have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hp : correctionScale t n ^ (2 * k n) ≤ correctionScale t n := by
      have hn : 1 ≤ 2 * k n := by have := hkpos n; omega
      simpa only [pow_one] using pow_le_pow_of_le_one hsnonneg hsone hn
    exact (herror n x v w).trans (by gcongr)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
