import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryEntropyError
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryJointMeasurable
import OAI.Analysis.LipschitzHilbert.Trees.BoundaryErrorFubini

namespace OAI

/-! Spatial integration of the expected original-minus-central packet
error. Joint measurability and product integrability are proved for the
literal finite packet sum on the fixed common good set. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_integrated_error (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (T : τ → SlopeBox) (w cutoff Kw D : ℝ)
    (hw : 0 < w) (hKw : 0 < Kw) (hD : 0 ≤ D) {K : ℕ} (hK : 0 < K)
    (M : τ → ℕ) (he : ∀ t ∈ tops, g.eligible cutoff (w/(T t).length) (M t))
    (a : ℝ) (ha : 0 ≤ a) (packets : Finset σ)
    (assigned : σ → τ) (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (stop : σ → ℕ) (value : (ℝ×ℝ) → σ → E)
    (hv : ∀ s, Measurable (fun x => value x s))
    (hmax : ∀ s ∈ packets, stop s ≤ M (assigned s))
    (A H : ℝ) (hA : 0 ≤ A) (μ : Measure (ℝ×ℝ)) [SFinite μ]
    (good : Set (ℝ×ℝ)) (hgood : MeasurableSet good)
    (hweight : IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight Kw D x) good μ)
    (hlog : ∀ x ∈ good, Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D x)) ≤ H)
    (hB : ∀ x ∈ good, ∀ t ∈ tops, ∀ k ≤ M t,
      ‖∑ s ∈ (packets.filter (fun s => assigned s = t)).filter (fun s => stop s ≤ k), value x s‖ ≤
        A*((T t).weight Kw D x)^8) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let C := 8*a*A*epsilon*((2:ℝ)^D)^7*(1+H)
    let err := fun z : ℝ×(ℝ×ℝ) => ‖(∑ s ∈ packets, value z.2 s)-
      ∑ s ∈ packets, (((g.withOrigin z.1).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x) K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a z.2 : ℝ):ℂ) • value z.2 s‖
    Integrable err ((volume.restrict (Ioc 0 g.rootWidth)).prod (μ.restrict good)) ∧
      IntervalIntegrable (fun origin => ∫ x in good, err (origin,x) ∂μ) volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, ∫ x in good, err (origin,x) ∂μ)/g.rootWidth ≤
        C*(∫ x in good, ∑ t ∈ tops, (T t).weight Kw D x ∂μ) := by
  intro epsilon C err
  have hbound (x : ℝ×ℝ) (hx : x ∈ good) :=
    g.source_boundary_expected_error_mass L hbranch hsmall tops T w cutoff Kw D hw hKw hD hK M he
      a ha x packets assigned hassigned stop (value x) hmax A H hA (hlog x hx) (hB x hx)
  have hm : Measurable err :=
    g.measurable_source_boundary_error_origin_point tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x)
      (fun t _ => (div_pos hw (T t).length_pos).le) (fun t x => (T t).weight_pos hKw D x)
      (fun t => ((T t).continuous_weight hKw D).measurable) hK (g.sourceBoundaryGap L)
      packets assigned stop hassigned
      (fun s hs => g.eligible_of_le (div_pos hw (T (assigned s)).length_pos).le
        (hmax s hs) (he (assigned s) (hassigned s hs))) a value hv
  have hfi : ∀ᵐ x ∂μ.restrict good,
      IntervalIntegrable (fun origin => err (origin,x)) volume 0 g.rootWidth := by
    filter_upwards [ae_restrict_mem hgood] with x hx
    exact (hbound x hx).1
  have havg : ∀ᵐ x ∂μ.restrict good,
      (∫ origin in (0:ℝ)..g.rootWidth, err (origin,x))/g.rootWidth ≤
        C*(∑ t ∈ tops, (T t).weight Kw D x) := by
    filter_upwards [ae_restrict_mem hgood] with x hx
    exact (hbound x hx).2
  have hb := nonnegative_translation_average_integral_le (μ.restrict good) g.rootWidth g.rootWidth_pos
    err hm (fun z => norm_nonneg _) hfi (fun x => C*(∑ t ∈ tops, (T t).weight Kw D x))
    (hweight.const_mul C) havg
  simpa only [integral_const_mul] using hb

end LipschitzHilbert.AngularGrid

end

end OAI
