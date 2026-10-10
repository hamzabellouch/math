import OAI.Analysis.FiniteFactor.CrossedProduct.TorusModel
import OAI.Analysis.FiniteFactor.OrbitSampling.TrimmedMarginals
import OAI.Analysis.FiniteFactor.OrbitSampling.TrimmedWeak

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceTorusEndpoint (r : Bool) (p : SourceSamplingTorus) : SourceTorus := if r then p.2 else p.1

theorem sourceTorusEndpoint_measurable (r : Bool) : Measurable (sourceTorusEndpoint r) := by
  cases r
  · exact measurable_fst
  · exact measurable_snd

theorem sourceSamplingTorus_marginal_transport (μ : Measure SourceSamplingPair) (r : Bool)
    (g : (SourceCoordinate → ℝ) → ℝ) (hg : Measurable g)
    (hm : μ.map (sourceSamplingEndpoint r) = sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x))) :
    (μ.map sourceSamplingTorusMap).map (sourceTorusEndpoint r) =
      sourceTorusHaar.withDensity (fun z => ENNReal.ofReal (g (sourceTorusRepresentative z))) := by
  have he : sourceTorusEndpoint r ∘ sourceSamplingTorusMap = sourceTorusQuotient ∘ sourceSamplingEndpoint r := by
    funext p
    cases r <;> rfl
  rw [Measure.map_map (sourceTorusEndpoint_measurable r) sourceSamplingTorusMap_continuous.measurable,he,
    ← Measure.map_map sourceTorusQuotient_preserving.measurable (sourceSamplingEndpoint_measurable r),hm]
  exact sourceTorusQuotient_withDensity _ hg.ennreal_ofReal

/-- The actual torus marginals, rather than only the representative-space
marginals, have uniformly bounded L2 densities with respect to product Haar. -/
theorem sourceSamplingTrimmed_torus_marginals_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ (I : Finset SourceCoordinate) (r : Bool), ∃ C : ℝ, ∀ s,
      ∃ g : SourceTorus → ℝ,
        Measurable g ∧ (∀ z, 0 ≤ g z) ∧
        (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus).map (sourceTorusEndpoint r) =
          sourceTorusHaar.withDensity (fun z => ENNReal.ofReal (g z)) ∧
        MemLp g 2 sourceTorusHaar ∧ (∫ z, g z^2 ∂sourceTorusHaar) ≤ C := by
  filter_upwards [sourceSamplingTrimmed_marginals_event] with θ hθ
  intro I r
  obtain ⟨C,hC⟩ := hθ I r
  refine ⟨C,fun s => ?_⟩
  obtain ⟨g,hg,hg0,hgm,hglp,hgint⟩ := hC s
  refine ⟨g ∘ sourceTorusRepresentative,hg.comp sourceTorusRepresentative_preserving.measurable,
    fun z => hg0 _,sourceSamplingTorus_marginal_transport _ r g hg hgm,?_,?_⟩
  · exact hglp.comp_measurePreserving sourceTorusRepresentative_preserving
  · have he : (∫ z, (g (sourceTorusRepresentative z))^2 ∂sourceTorusHaar) =
        ∫ x, g x^2 ∂sourceSamplingHaar := by
      rw [← sourceTorusRepresentative_preserving.map_eq]
      exact (integral_map sourceTorusRepresentative_preserving.measurable.aemeasurable
        (hg.pow_const 2).aestronglyMeasurable).symm
    exact he.trans_le hgint

end
end FiniteFactor

end OAI
