import OAI.Analysis.LienardCycles.QuadraticSlices

namespace OAI

universe uP

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.WidthTransport
open ScalarArcs CanonicalVariation WidthCoordinates PartialCalculus
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : ArcFamilies.State P, ∃ f : ArcFamilies.State P × ℝ → ArcFamilies.State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (ArcFamilies.field Φ (f q)) q.2)
include hΦ hloc

theorem base_width_deriv {p : P} {t r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => baseAtWidth Φ ((p,t),s))
      (-(r^2-(M Φ p (baseAtWidth Φ ((p,t),r),r))^2)/r) r := by
  let h := baseAtWidth Φ ((p,t),r)
  have hs := base_spec Φ hΦ hloc (p := p) (t := t) hr
  let f : ℝ → ℝ := fun h => widthFamily Φ ((p,t),h)
  let g : ℝ → ℝ := fun s => baseAtWidth Φ ((p,t),s)
  have hg : DifferentiableAt ℝ g r :=
    ((base_analytic Φ hΦ hloc hr).comp r
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hf := width_base_deriv Φ hΦ hloc (p := p) hs.1
  have hm := midpoint_reparam Φ hΦ hloc (p := p) hs.1
  rw [hs.2] at hm hf
  rw [←hm] at hf
  have he : (f ∘ g) =ᶠ[𝓝 r] id := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hsr
    exact (base_spec Φ hΦ hloc hsr).2
  have hc := (hf.comp r hg.hasDerivAt).unique
    ((hasDerivAt_id r).congr_of_eventuallyEq he)
  have hgap := ne_of_gt (M_gap_pos Φ hΦ hloc (p := p) (h := h) hr)
  have hg' : deriv g r = -(r^2-M Φ p (h,r)^2)/r := by
    change (-r / (r^2-M Φ p (h,r)^2))*deriv g r = 1 at hc
    field_simp [hgap, ne_of_gt hr] at hc ⊢
    nlinarith [hc]
  simpa only [hg'] using hg.hasDerivAt

end QuinticLienard.WidthTransport

end OAI
