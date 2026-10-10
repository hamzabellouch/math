import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BoundedRegionTests

namespace OAI

/-!
# Lower mass bounds for radial cutoffs

A radial cutoff equal to one on a smaller ball transfers its mass lower bound to
the squared-cutoff integral on a larger ball. For source measures with growing
support diameters, the prescribed lower growth estimate supplies this bound eventually.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem radial_cutoff_mass_of_ball_mass {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R c : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hc : 0 ≤ c)
    (hmass : ENNReal.ofReal c ≤ μ (ball a r)) :
    c ≤ ∫ x in ball a R, (radialUnitCutoff a r x) ^ 2 ∂μ := by
  let := finiteMeasure_restrict_ball_of_globalGrowth n G μ hg a R (hr.trans_le hrR)
  have hfin : μ (ball a r) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hg.2 a r hr)
  have hreal : c ≤ (μ (ball a r)).toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hmass
    simpa only [ENNReal.toReal_ofReal hc] using! h
  have hcut := cutoff_mass_lower_of_one_on (μ.restrict (ball a R))
    (radialUnitCutoff a r) (radialUnitCutoff_lipschitz a r).continuous.measurable
    (fun x => by
      rw [abs_of_nonneg (radialUnitCutoff_bounds a r x).1]
      exact (radialUnitCutoff_bounds a r x).2)
    (ball a r) measurableSet_ball (fun x hx => radialUnitCutoff_eq_one a r x hx.le)
  have hrestrict : (μ.restrict (ball a R)).real (ball a r) = (μ (ball a r)).toReal := by
    rw [Measure.real, Measure.restrict_apply measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball hrR)]
  rw [hrestrict] at hcut
  exact hreal.trans hcut

theorem source_radial_cutoff_mass_eventually {d : ℕ} (n : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (a : Ambient d) (hC : 0 < C)
    (hlower : ∀ j r, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball a r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ∀ᶠ j in atTop, r ^ n / C ≤
      ∫ x in ball a R, (radialUnitCutoff a r x) ^ 2 ∂μ j := by
  filter_upwards [hdiam r hr] with j hj
  exact radial_cutoff_mass_of_ball_mass n G (μ j) (hg j) a r R (r ^ n / C)
    hr hrR (by positivity) (hlower j r ⟨hr, hj⟩)

end

end RieszRectifiability

end OAI
