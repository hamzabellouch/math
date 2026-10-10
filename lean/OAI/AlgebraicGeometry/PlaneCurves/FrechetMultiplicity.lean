import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FunProp

namespace OAI

/-!
# Frechet derivatives, transverse jets, and analytic multiplicity
-/

section

/-!
# Analytic Taylor-derivative form of multiplicity descent

The hypotheses use the total Fréchet derivatives. Their vanishing implies
the univariate jet condition after restriction to a transverse line.
-/
namespace Nagata.W19

open scoped Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- One constant directional derivative lowers total Taylor vanishing order by at most one. -/
theorem directional_derivative_taylor_vanishing
    {H : E → ℂ} {p : E} (hH : AnalyticAt ℂ H p) (v : E) (m : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H p = 0) :
    ∀ n, n + 1 < m →
      iteratedFDeriv ℂ n (fun z => fderiv ℂ H z v) p = 0 := by
  intro n hn
  have hz : iteratedFDeriv ℂ n (fderiv ℂ H) p = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_fderiv, hvan (n + 1) hn, norm_zero]
  change iteratedFDeriv ℂ n ((ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ H) p = 0
  rw [(ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left
    (hH.fderiv.contDiffAt (n := (n : WithTop ℕ∞))) le_rfl, hz]
  ext w
  simp

/-- Repeated constant directional differentiation as a genuine derivative operator. -/
noncomputable def directionalIterate (v : E) : ℕ → (E → ℂ) → E → ℂ
  | 0, H => H
  | b + 1, H => directionalIterate v b (fun z => fderiv ℂ H z v)

theorem directionalIterate_analyticAt {H : E → ℂ} {p : E}
    (hH : AnalyticAt ℂ H p) (v : E) (b : ℕ) :
    AnalyticAt ℂ (directionalIterate v b H) p := by
  induction b generalizing H with
  | zero => exact hH
  | succ b ih =>
    apply ih
    exact ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hH.fderiv

/-- Any number of directional derivatives reduces the total Taylor order by at most that number. -/
theorem directionalIterate_taylor_vanishing {H : E → ℂ} {p : E}
    (hH : AnalyticAt ℂ H p) (v : E) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H p = 0) :
    ∀ n, n + b < m → iteratedFDeriv ℂ n (directionalIterate v b H) p = 0 := by
  induction b generalizing H m with
  | zero => simpa [directionalIterate] using hvan
  | succ b ih =>
    have ha : AnalyticAt ℂ (fun z => fderiv ℂ H z v) p :=
      ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hH.fderiv
    have hv : ∀ n < m - 1, iteratedFDeriv ℂ n (fun z => fderiv ℂ H z v) p = 0 := by
      intro n hn
      exact directional_derivative_taylor_vanishing hH v m hvan n (by omega)
    intro n hn
    exact ih ha (m - 1) hv n (by omega)

/-- Analytic pullback preserves vanishing of total Taylor derivatives. -/
theorem analytic_pullback_taylor_vanishing
    [CompleteSpace E]
    {H : E → ℂ} {p : ℂ} {γ : ℂ → E}
    (hH : AnalyticAt ℂ H (γ p)) (hγ : AnalyticAt ℂ γ p)
    (m : ℕ) (hvan : ∀ n < m, iteratedFDeriv ℂ n H (γ p) = 0) :
    ∀ n < m, iteratedFDeriv ℂ n (H ∘ γ) p = 0 := by
  intro n hn
  rw [iteratedFDeriv_comp (hH.contDiffAt (n := (n : WithTop ℕ∞)))
    (hγ.contDiffAt (n := (n : WithTop ℕ∞))) le_rfl]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_eq_zero
  intro c _
  ext
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries]
  rw [hvan c.length (lt_of_le_of_lt c.length_le hn)]
  simp

/-- The Taylor-derivative form of ordinary bivariate multiplicity yields the
required univariate analytic order after transverse differentiation. -/
theorem transverse_restriction_order_of_total_taylor_vanishing
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ)
    (hH : AnalyticAt ℂ H (ξ, 0)) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H (ξ, 0) = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => directionalIterate (0, 1) b H (x, 0)) ξ := by
  let G := directionalIterate (0, 1) b H
  have hG : AnalyticAt ℂ G (ξ, 0) := directionalIterate_analyticAt hH (0, 1) b
  have hγ : AnalyticAt ℂ (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG.comp (f := fun x : ℂ => (x, (0 : ℂ))) (x := ξ) hγ)).mpr
  intro n hn
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hv : ∀ j < m - b, iteratedFDeriv ℂ j G (ξ, 0) = 0 := by
    intro j hj
    exact directionalIterate_taylor_vanishing hH (0, 1) m b hvan j (by omega)
  have hz := analytic_pullback_taylor_vanishing (γ := fun x : ℂ => (x, (0 : ℂ))) (p := ξ) hG hγ (m - b) hv n hn
  simpa only [Function.comp_def, zero_apply] using congrArg (fun L => L (fun _ => (1 : ℂ))) hz

/-- Repeated transverse Fréchet differentiation is the ordinary repeated
one-variable derivative in the second coordinate. -/
theorem directionalIterate_vertical_eq_iteratedDeriv
    {H : (ℂ × ℂ) → ℂ} {x y : ℂ} (hH : AnalyticAt ℂ H (x, y)) (b : ℕ) :
    directionalIterate (0, 1) b H (x, y) =
      iteratedDeriv b (fun t => H (x, t)) y := by
  induction b generalizing H with
  | zero => simp [directionalIterate]
  | succ b ih =>
    let G : (ℂ × ℂ) → ℂ := fun z => fderiv ℂ H z (0, 1)
    have hG : AnalyticAt ℂ G (x, y) := by
      change AnalyticAt ℂ ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)) ∘
        fderiv ℂ H) (x, y)
      exact ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)).analyticAt _).comp hH.fderiv
    have hc : ContinuousAt (fun t : ℂ => (x, t)) y := by fun_prop
    have hev : ∀ᶠ t in 𝓝 y, AnalyticAt ℂ H (x, t) :=
      hc.tendsto.eventually hH.eventually_analyticAt
    have heq : (fun t => deriv (fun u => H (x, u)) t) =ᶠ[𝓝 y]
        (fun t => G (x, t)) := by
      filter_upwards [hev] with t ht
      have hline : HasDerivAt (fun u : ℂ => (x, u)) (0, 1) t :=
        by simpa using ((hasFDerivAt_const (𝕜 := ℂ) x t).prodMk
          (hasFDerivAt_id t)).hasDerivAt
      exact (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt t hline).deriv
    change directionalIterate (0, 1) b G (x, y) = _
    rw [ih hG, iteratedDeriv_succ']
    exact (Filter.EventuallyEq.iteratedDeriv_eq b heq).symm

/-- Actual transverse iterated derivatives satisfy the collision order bound
from total Fréchet Taylor vanishing, including identically zero functions. -/
theorem transverse_iteratedDeriv_order_of_total_taylor_vanishing
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ)
    (hH : AnalyticAt ℂ H (ξ, 0)) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H (ξ, 0) = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  have hc : ContinuousAt (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  have hev : ∀ᶠ x in 𝓝 ξ, AnalyticAt ℂ H (x, 0) :=
    hc.tendsto.eventually hH.eventually_analyticAt
  have heq : (fun x => directionalIterate (0, 1) b H (x, 0)) =ᶠ[𝓝 ξ]
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) := by
    filter_upwards [hev] with x hx
    exact directionalIterate_vertical_eq_iteratedDeriv hx b
  rw [← analyticOrderAt_congr heq]
  exact transverse_restriction_order_of_total_taylor_vanishing ξ hH m b hvan

end Nagata.W19

end

section

namespace Nagata.W19

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem derivSeries_coeff_zero
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : FormalMultilinearSeries ℂ E F) (n : ℕ) (hzero : P (n + 1) = 0) :
    P.derivSeries n = 0 := by
  have hz' : ∀ j, j = n + 1 → P j = 0 := by
    intro j hj
    subst j
    exact hzero
  have hz : P (1 + n) = 0 := hz' (1 + n) (Nat.add_comm 1 n)
  ext v w
  simp [FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    FormalMultilinearSeries.changeOriginSeries,
    FormalMultilinearSeries.changeOriginSeriesTerm, hz]

private theorem iteratedFDeriv_zero_of_series_coeff (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
      {H : E → F} {p : E} {P : FormalMultilinearSeries ℂ E F},
      HasFPowerSeriesAt H P p → P n = 0 → iteratedFDeriv ℂ n H p = 0 := by
  induction n with
  | zero =>
    intro F _ _ _ H p P hP hzero
    ext v
    simpa [hzero] using (hP.coeff_zero v).symm
  | succ n ih =>
    intro F _ _ _ H p P hP hzero
    obtain ⟨r, hr⟩ := hP
    have hd : P.derivSeries n = 0 := derivSeries_coeff_zero P n hzero
    have hi := ih (F := E →L[ℂ] F) hr.fderiv.hasFPowerSeriesAt hd
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hi, norm_zero]

/-- Vanishing actual convergent power-series coefficients implies vanishing
of total derivatives below that order. -/
theorem total_taylor_vanishing_of_powerSeries
    {H : E → ℂ} {p : E} {P : FormalMultilinearSeries ℂ E ℂ}
    (hP : HasFPowerSeriesAt H P p) (m : ℕ) (hzero : ∀ n < m, P n = 0) :
    ∀ n < m, iteratedFDeriv ℂ n H p = 0 := by
  intro n hn
  exact iteratedFDeriv_zero_of_series_coeff n hP (hzero n hn)

/-- Ordinary analytic power-series multiplicity gives the transverse order
needed by the moving-center collision theorem. -/
theorem transverse_iteratedDeriv_order_of_powerSeries
    {H : (ℂ × ℂ) → ℂ} {P : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ}
    (ξ : ℂ) (hP : HasFPowerSeriesAt H P (ξ, 0))
    (m b : ℕ) (hzero : ∀ n < m, P n = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  apply transverse_iteratedDeriv_order_of_total_taylor_vanishing ξ ⟨P, hP⟩ m b
  exact total_taylor_vanishing_of_powerSeries hP m hzero

end Nagata.W19

end

section

namespace Nagata.W19
open scoped Topology
open Filter

/-- Transverse derivatives restricted to the horizontal line are analytic. -/
theorem analyticAt_transverse_iteratedDeriv
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ) (hH : AnalyticAt ℂ H (ξ, 0)) (b : ℕ) :
    AnalyticAt ℂ (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  have hγ : AnalyticAt ℂ (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  have hG := (directionalIterate_analyticAt hH (0, 1) b).comp
    (f := fun x : ℂ => (x, (0 : ℂ))) (x := ξ) hγ
  apply hG.congr
  have hev : ∀ᶠ x in 𝓝 ξ, AnalyticAt ℂ H (x, 0) :=
    hγ.continuousAt.tendsto.eventually hH.eventually_analyticAt
  filter_upwards [hev] with x hx
  exact directionalIterate_vertical_eq_iteratedDeriv hx b

/-- Explicit mixed derivative vanishing from actual convergent Taylor coefficients. -/
theorem mixed_iteratedDeriv_zero_of_powerSeries
    {H : (ℂ × ℂ) → ℂ} {P : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ}
    (ξ : ℂ) (hP : HasFPowerSeriesAt H P (ξ, 0)) (m : ℕ)
    (hzero : ∀ n < m, P n = 0) (ell b : ℕ) (hlt : ell + b < m) :
    iteratedDeriv ell (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ = 0 := by
  have ha := analyticAt_transverse_iteratedDeriv ξ ⟨P, hP⟩ b
  have ho := transverse_iteratedDeriv_order_of_powerSeries ξ hP m b hzero
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).mp ho ell (by omega)

end Nagata.W19

end

end OAI
