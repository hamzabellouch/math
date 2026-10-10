import Mathlib
import OAI.Geometry.CAT0Fillings.Calculus.PositiveExtension
import OAI.Geometry.CAT0Fillings.Calculus.Truncation

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

lemma clamp_gradient_scalar {E : Type*} [Zero E] {t ε N : ℝ} (hεN : ε < N) (v : E) :
    (if ε < min t N then (if t < N then v else 0) else 0) =
      (if ε < t ∧ t < N then v else 0) := by
  by_cases he : ε < t <;> by_cases ht : t < N <;> simp [lt_min_iff,he,ht,hεN]
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma closed_clamp (hz : IsCycle T) (P : q.Sobolev) {ε N : ℝ} (hεN : ε < N) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => max (min (q.inclusion P x) N) ε) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if ε < q.inclusion P (q.atlasParam w) ∧ q.inclusion P (q.atlasParam w) < N
          then q.closedGradient P w else 0) := by
  obtain ⟨U,hU,hUG⟩ := q.closed_min_const hz P N
  obtain ⟨V,hV,hVG⟩ := q.closed_max_const hz U ε
  refine ⟨V,?_,?_⟩
  · filter_upwards [hU,hV] with x hu hv
    rw [hv,hu]
  · have hau := q.atlas_preserving.quasiMeasurePreserving.ae
      (p := fun x : X => q.inclusion U x = min (q.inclusion P x) N) hU
    filter_upwards [hau,hUG,hVG] with w hu hug hvg
    rw [hvg,hu,hug]
    exact clamp_gradient_scalar hεN _

lemma closed_positive_bivariate {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {R : ℝ} (hrange : ∀ x, 0 ≤ r x ∧ r x ≤ R)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F {z | 0 < z.2})
    (P : q.Sobolev) {ε N : ℝ} (he : 0 < ε) (hN : ε ≤ N)
    (hb : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, q.inclusion P x ∈ Icc ε N) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,q.inclusion P x)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),q.inclusion P (q.atlasParam w)) (0,1) • q.closedGradient P w) := by
  obtain ⟨G,hG,heq⟩ := positive_strip_extension hF he hN
  have hbound : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ‖(r x,q.inclusion P x)‖ ≤ max R N := by
    filter_upwards [hb] with x hx
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (hrange x).1,abs_of_nonneg (he.le.trans hx.1)]
    exact max_le_max (hrange x).2 hx.2
  obtain ⟨Q,hQ,hQG⟩ := q.closed_bounded_bivariate hr hG P hbound
  refine ⟨Q,?_,?_⟩
  · filter_upwards [hQ,hb] with x hx hb
    rw [hx,(heq _ hb).eq_of_nhds]
  · have ha := q.atlas_preserving.quasiMeasurePreserving.ae
      (p := fun x : X => q.inclusion P x ∈ Icc ε N) hb
    filter_upwards [hQG,ha] with w hw ha
    rw [hw,(heq _ ha).fderiv_eq]

lemma closed_positive_clamped_bivariate (hz : IsCycle T)
    {r : X → ℝ} {K : ℝ≥0} (hr : LipschitzWith K r)
    {R : ℝ} (hrange : ∀ x, 0 ≤ r x ∧ r x ≤ R)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F {z | 0 < z.2})
    (P : q.Sobolev) {ε N : ℝ} (he : 0 < ε) (hN : ε < N) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F (r x,max (min (q.inclusion P x) N) ε)) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => fderiv ℝ F (r (q.atlasParam w),max (min (q.inclusion P (q.atlasParam w)) N) ε) (1,0) • q.gradient hr w +
          fderiv ℝ F (r (q.atlasParam w),max (min (q.inclusion P (q.atlasParam w)) N) ε) (0,1) •
            (if ε < q.inclusion P (q.atlasParam w) ∧ q.inclusion P (q.atlasParam w) < N
              then q.closedGradient P w else 0)) := by
  obtain ⟨U,hU,hUG⟩ := q.closed_clamp hz P hN
  have hbound : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, q.inclusion U x ∈ Icc ε N := by
    filter_upwards [hU] with x hx
    rw [hx]
    exact ⟨le_max_right _ _,max_le (min_le_right _ _) hN.le⟩
  obtain ⟨Q,hQ,hG⟩ := q.closed_positive_bivariate hr hrange hF U he hN.le hbound
  refine ⟨Q,?_,?_⟩
  · filter_upwards [hQ,hU] with x hq hu
    rw [hq,hu]
  · have hau := q.atlas_preserving.quasiMeasurePreserving.ae
      (p := fun x : X => q.inclusion U x = max (min (q.inclusion P x) N) ε) hU
    filter_upwards [hG,hau,hUG] with w hq hu hug
    simp only [hq,hu,hug]
end CAT0Fillings.ChartGeometry
end

end OAI
