import OAI.Geometry.SurfaceImmersion.Whitney.CompactCollarJet
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisCurve

namespace OAI

/-! A compact homotopy of transverse boundary vectors gives an actual
 smooth regular collar agreeing with its two endpoint ruled collars. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem regular_homotopy_collar {c : ℝ → W} {V : ℝ × ℝ → W}
    (hc : ContDiff ℝ ∞ c) (hV : ContDiff ℝ ∞ V) {a b : ℝ}
    (hI : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc a b,
      Function.Injective (homotopyCollarJet c V s t 0 0)) :
    ∃ (r : ℝ) (χ : ℝ → ℝ), 0 < r ∧ ContDiff ℝ ∞ χ ∧
      tsupport χ ⊆ Icc (-r) r ∧
      ContDiff ℝ ∞ (homotopyCollar c V χ) ∧
      (∀ u : ℝ, |u| < r → ∀ t ∈ Icc a b,
        Function.Injective (fderiv ℝ (homotopyCollar c V χ) ![u,t])) ∧
      (∀ t, homotopyCollar c V χ =ᶠ[𝓝 (crosscapAxis t)]
        fun x => c (x 1)+x 0 • V (1,x 1)) ∧
      ∀ x : Base, r < |x 0| → homotopyCollar c V χ =ᶠ[𝓝 x]
        fun y => c (y 1)+y 0 • V (0,y 1) := by
  obtain ⟨δ,hδ,hstable⟩ := compact_collar_jet hc hV (isCompact_Icc.prod isCompact_Icc)
    (by rintro ⟨s,t⟩ ⟨hs,ht⟩; exact hI s hs t ht)
  obtain ⟨χ,hχ,_hcomp,hg,hs,hrange,hsmall⟩ :=
    exists_slow_collar_cutoff (half_pos hδ) hδ
  refine ⟨δ/2,χ,half_pos hδ,hχ,hs,homotopyCollar_smooth hc hV hχ,?_,?_,?_⟩
  · intro u hu t ht
    rw [homotopyCollar_fderiv hc hV hχ]
    apply hstable (χ u,t) ⟨hrange u,ht⟩ u (u*deriv χ u)
      (hu.trans (half_lt_self hδ)) (hsmall u)
  · intro t
    have hp : Tendsto (fun x : Base => x 0) (𝓝 (crosscapAxis t)) (𝓝 0) := by
      simpa [crosscapAxis_apply] using (continuous_apply (0 : Fin 2)).continuousAt.tendsto (x := crosscapAxis t)
    filter_upwards [hg.comp_tendsto hp] with x hx
    change c (x 1)+x 0 • V (χ (x 0),x 1) = _
    change χ (x 0) = 1 at hx
    rw [hx]
  · intro x hx
    have hn : x 0 ∉ tsupport χ := by
      intro h
      have hh := abs_le.mpr (hs h)
      exact hx.not_ge hh
    have hp : Tendsto (fun y : Base => y 0) (𝓝 x) (𝓝 (x 0)) :=
      (continuous_apply (0 : Fin 2)).continuousAt.tendsto
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hp] with y hy
    change c (y 1)+y 0 • V (χ (y 0),y 1) = _
    change χ (y 0) = 0 at hy
    rw [hy]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
