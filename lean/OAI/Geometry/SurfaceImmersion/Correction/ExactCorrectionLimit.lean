import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

namespace OAI

/-!
# Passing the correction sequence to a smooth isometric limit

A correction sequence with eventually summable bounds at every derivative
order converges smoothly in coordinate space. Convergence of its pullback
metrics then gives an isometric immersion whenever the limiting metric is
positive definite.
-/

noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

open Filter
open scoped Topology ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Finite-stage maps, with the initial map kept separate from the corrections. -/
def partialMap (F : E → V) (U : ℕ → E → V) (N : ℕ) (x : E) : V :=
  F x + ∑ n ∈ Finset.range N, U n x

/-- The limit map defined by the convergent correction series. -/
def limitMap (F : E → V) (U : ℕ → E → V) (x : E) : V :=
  F x + ∑' n, U n x

/-- Each derivative order only needs a summable bound after a finite waiting
period. This is why the initial, uncontrolled high derivatives cause no problem. -/
theorem smooth_limitMap {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n)) (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ n) :
    ContDiff ℝ ∞ (limitMap F U) := by
  apply hF.add
  apply contDiff_tsum_of_eventually (N := ⊤) hU (fun _ _ => hρ)
  intro m _
  simpa only [Nat.cofinite_eq_atTop] using hbound m

/-- Derivatives of the sum are the sums of the derivatives even though their
uniform bound is only eventually available. -/
theorem hasFDerivAt_limitMap {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n)) (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ n) (x : E) :
    HasFDerivAt (limitMap F U)
      (fderiv ℝ F x + ∑' n, fderiv ℝ (U n) x) x := by
  have hb0 : ∀ᶠ n in atTop, ∀ y ∈ (Set.univ : Set E), ‖U n y‖ ≤ ρ n := by
    filter_upwards [hbound 0] with n hn y _
    simpa only [norm_iteratedFDeriv_zero] using hn y
  have hb1 : ∀ᶠ n in atTop, ∀ y ∈ (Set.univ : Set E),
      ‖fderiv ℝ (U n) y‖ ≤ ρ n := by
    filter_upwards [hbound 1] with n hn y _
    simpa only [norm_iteratedFDeriv_one] using hn y
  have hval := tendstoUniformlyOn_tsum_nat_eventually hρ hb0
  have hder := tendstoUniformlyOn_tsum_nat_eventually hρ hb1
  have hs : HasFDerivAt (fun y => ∑' n, U n y)
      (∑' n, fderiv ℝ (U n) x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn isOpen_univ hder
    · intro N y _
      exact HasFDerivAt.fun_sum fun n _ =>
        ((hU n).differentiable (by simp) y).hasFDerivAt
    · intro y hy
      exact hval.tendsto_at hy
    · exact Set.mem_univ x
  exact ((hF.differentiable (by simp) x).hasFDerivAt.add hs)

/-- The finite-stage differential converges in operator norm. -/
theorem tendsto_fderiv_partialMap {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n)) (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ n) (x : E) :
    Tendsto (fun N => fderiv ℝ (partialMap F U N) x) atTop
      (𝓝 (fderiv ℝ (limitMap F U) x)) := by
  have hb1 : ∀ᶠ n in atTop, ∀ y ∈ (Set.univ : Set E),
      ‖fderiv ℝ (U n) y‖ ≤ ρ n := by
    filter_upwards [hbound 1] with n hn y _
    simpa only [norm_iteratedFDeriv_one] using hn y
  have hder := (tendstoUniformlyOn_tsum_nat_eventually hρ hb1).tendsto_at (Set.mem_univ x)
  have hfinite (N : ℕ) : fderiv ℝ (partialMap F U N) x =
      fderiv ℝ F x + ∑ n ∈ Finset.range N, fderiv ℝ (U n) x := by
    exact ((hF.differentiable (by simp) x).hasFDerivAt.add
      (HasFDerivAt.fun_sum fun n _ =>
        ((hU n).differentiable (by simp) x).hasFDerivAt)).fderiv
  simp_rw [hfinite]
  rw [(hasFDerivAt_limitMap hF hU hρ hbound x).fderiv]
  exact tendsto_const_nhds.add hder

/-- The pullback metric is continuous under the differential convergence just
proved, so a vanishing metric defect gives the exact desired metric. -/
theorem limitMap_metric {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n)) (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ n)
    (g : E → E → E → ℝ)
    (hmetric : ∀ x v w, Tendsto
      (fun N => inner ℝ (fderiv ℝ (partialMap F U N) x v)
        (fderiv ℝ (partialMap F U N) x w)) atTop (𝓝 (g x v w))) :
    ∀ x v w, inner ℝ (fderiv ℝ (limitMap F U) x v)
      (fderiv ℝ (limitMap F U) x w) = g x v w := by
  intro x v w
  have hd := tendsto_fderiv_partialMap hF hU hρ hbound x
  have hv := ((ContinuousLinearMap.apply ℝ V v).continuous.tendsto _).comp hd
  have hw := ((ContinuousLinearMap.apply ℝ V w).continuous.tendsto _).comp hd
  exact tendsto_nhds_unique (hv.inner hw) (hmetric x v w)

/-- Quantitative metric defects tending to zero imply the metric convergence
needed above. The bound is the bilinear operator-norm form of the residual
estimate produced by the correction iteration. -/
theorem limitMap_metric_of_error_bound
    {F : E → V} {U : ℕ → E → V} {ρ ε : ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n)) (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ n)
    (g : E → E → E → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (herror : ∀ n x v w,
      |inner ℝ (fderiv ℝ (partialMap F U n) x v)
        (fderiv ℝ (partialMap F U n) x w) - g x v w| ≤ ε n * ‖v‖ * ‖w‖) :
    ∀ x v w, inner ℝ (fderiv ℝ (limitMap F U) x v)
      (fderiv ℝ (limitMap F U) x w) = g x v w := by
  apply limitMap_metric hF hU hρ hbound g
  intro x v w
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (show Tendsto (fun n => ε n * ‖v‖ * ‖w‖) atTop (𝓝 0) from by
      simpa only [zero_mul] using (hε.mul_const ‖v‖).mul_const ‖w‖)
  simpa only [Real.norm_eq_abs] using herror n x v w

/-- Positive definiteness supplies injectivity; no separate rank estimate is
needed after the metric has passed to the limit. -/
theorem limitMap_immersion {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n)) (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ n)
    (g : E → E → E → ℝ)
    (hmetric : ∀ x v w, Tendsto
      (fun N => inner ℝ (fderiv ℝ (partialMap F U N) x v)
        (fderiv ℝ (partialMap F U N) x w)) atTop (𝓝 (g x v w)))
    (hpos : ∀ x v, v ≠ 0 → 0 < g x v v) :
    ContDiff ℝ ∞ (limitMap F U) ∧
      ∀ x, Function.Injective (fderiv ℝ (limitMap F U) x) := by
  refine ⟨smooth_limitMap hF hU hρ hbound, ?_⟩
  have hm := limitMap_metric hF hU hρ hbound g hmetric
  intro x v w hvw
  apply sub_eq_zero.mp
  by_contra hne
  have hz : fderiv ℝ (limitMap F U) x (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hp := hm x (v - w) (v - w)
  rw [hz, inner_zero_left] at hp
  exact (ne_of_gt (hpos x (v - w) hne)) hp.symm

end ClosedSurfaceR4.ExactCorrection

end

end OAI
