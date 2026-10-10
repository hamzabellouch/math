import OAI.Analysis.LipschitzHilbert.Trees.SourceRadialIntegral

namespace OAI

/-! A radial one-level loss is cut off to the near-boundary region.
It is measurable and uniformly bounded by the fixed total/self log ratio. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

def radialBoundaryLoss (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (epsilon : ℝ) (i : ℕ) (top : τ) (x : X) : ℝ → ℝ :=
  (Ioo 0 epsilon).indicator (fun b => Real.log
    (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
      g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x))

theorem radialBoundaryLoss_measurable (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (epsilon : ℝ) (i : ℕ) (top : τ) (x : X) :
    Measurable (g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x) :=
  ((measurable_const.div ((g.nearbyEligibleMass_measurable_radius tops slope precision cutoff
    weight i (slope top) x).comp (measurable_id.mul_const (g.width i)))).log).indicator measurableSet_Ioo

theorem radialBoundaryLoss_bounds (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (i : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) i) (x : X) (b : ℝ) :
    0 ≤ g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b ∧
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b ≤
        Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  have hw0 := hw top x
  have htotal : weight top x ≤ ∑ t ∈ tops, weight t x :=
    Finset.single_le_sum (fun t _ => (hw t x).le) htop
  have hBlog := Real.log_nonneg ((one_le_div hw0).mpr htotal)
  by_cases hb : b ∈ Ioo 0 epsilon
  · rw [radialBoundaryLoss,indicator_of_mem hb]
    have hself := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
      (fun t x => (hw t x).le) i top htop he (mul_pos hb.1 (g.width_pos i)) x
    have hinner : 0 < g.nearbyEligibleMass tops slope precision cutoff weight i
        (b*g.width i) (slope top) x := hw0.trans_le hself
    have houter := g.nearbyEligibleMass_le_total tops slope precision cutoff weight
      (fun t x => (hw t x).le) i (epsilon*g.width i) (slope top) x
    have horder := g.nearbyEligibleMass_le_of_scale (i := i) (j := i) tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) le_rfl (mul_le_mul_of_nonneg_right hb.2.le (g.width_pos i).le)
      (slope top) x
    refine ⟨Real.log_nonneg ((one_le_div hinner).mpr horder),?_⟩
    apply Real.log_le_log (div_pos (hinner.trans_le horder) hinner)
    exact div_le_div₀ (hw0.trans_le htotal).le houter hw0 hself
  · rw [radialBoundaryLoss,indicator_of_notMem hb]
    exact ⟨le_rfl,hBlog⟩

theorem radialBoundaryLoss_intervalIntegrable (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (i : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) i) (x : X) (a b : ℝ) :
    IntervalIntegrable (g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x)
      volume a b := by
  have hi (a b : ℝ) : IntegrableOn
      (g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x) (Ioc a b) volume := by
    apply (integrableOn_const (μ := volume) (C := Real.log ((∑ t ∈ tops, weight t x)/weight top x))
      (by simp)).mono' (g.radialBoundaryLoss_measurable tops slope precision cutoff weight epsilon i top x).aestronglyMeasurable
    filter_upwards [] with u
    have hu := g.radialBoundaryLoss_bounds tops slope precision cutoff weight hp hw epsilon i top htop he x u
    rw [Real.norm_eq_abs,abs_of_nonneg hu.1]
    exact hu.2
  exact ⟨hi a b,hi b a⟩

end LipschitzHilbert.AngularGrid

end

end OAI
