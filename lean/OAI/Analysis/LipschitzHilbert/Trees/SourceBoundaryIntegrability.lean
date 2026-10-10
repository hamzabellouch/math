import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryJointMeasurable

namespace OAI

/-! Every fixed-translation boundary sum is integrable whenever its
original finite packet values are integrable. This supplies all sections
needed for recovery, in addition to the averaged Fubini estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℂ E]

theorem source_boundary_sum_integrable (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwm : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K)
    (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (he : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a : ℝ) (ha : 0 ≤ a) (μ : Measure X) (value : X → σ → E)
    (hvalue : ∀ s ∈ packets, Integrable (fun x => value x s) μ) (origin : ℝ) :
    Integrable (fun x => ∑ s ∈ packets,
      (((g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x : ℝ):ℂ) • value x s) μ := by
  apply integrable_finsetSum
  intro s hs
  have hm := (g.measurable_sourceBoundaryCoefficient_origin_point tops slope precision cutoff
    weight hp hw hwm hK gap (stop s) (assigned s) (hassigned s hs) (he s hs) a).comp
      (measurable_const.prodMk measurable_id : Measurable (fun x : X => (origin,x)))
  have hb : ∀ᵐ x ∂μ,
      ‖(((g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x : ℝ):ℂ)‖ ≤ 1 := by
    filter_upwards [] with x
    have h := (g.withOrigin origin).sourceBoundaryCoefficient_bounds tops slope precision cutoff
      weight hp hw hK gap (stop s) (assigned s) (hassigned s hs) (he s hs) a ha x
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos h.1] using h.2
  exact (hvalue s hs).bdd_smul 1 hm.complex_ofReal.aestronglyMeasurable hb

end LipschitzHilbert.AngularGrid

end

end OAI
