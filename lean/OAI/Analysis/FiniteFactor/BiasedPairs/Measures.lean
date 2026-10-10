import OAI.Analysis.FiniteFactor.CrossedProduct.StageCoupling
import OAI.Analysis.FiniteFactor.OrbitSampling.TorusMarginals
import OAI.Analysis.FiniteFactor.Coupling.Order
import OAI.Analysis.FiniteFactor.Coupling.VectorBayes

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal Topology
noncomputable section

abbrev SourceBiasedSample := SourceCoordinate → Fin 6 × (ℝ × ℝ)
abbrev sourceBiasedLaw (j : ℕ) : Measure SourceBiasedSample :=
  blockProductCoupling (stagedCouplingParameters j) sourceBlockSize

def sourceBiasedEndpoint (r : SourceCoordinate → Bool) : SourceBiasedSample → (SourceCoordinate → ℝ) :=
  blockProductEndpoint r

theorem sourceBiasedEndpoint_measurable (r : SourceCoordinate → Bool) :
    Measurable (sourceBiasedEndpoint r) := vectorEndpoint_measurable r

/-- The mixed pair has the original x endpoint and selects x or y coordinatewise. -/
def sourceBiasedPair (r : SourceCoordinate → Bool) (ω : SourceBiasedSample) : SourceSamplingPair :=
  (sourceBiasedEndpoint (fun _ => false) ω,sourceBiasedEndpoint r ω)

theorem sourceBiasedPair_measurable (r : SourceCoordinate → Bool) : Measurable (sourceBiasedPair r) :=
  (sourceBiasedEndpoint_measurable _).prodMk (sourceBiasedEndpoint_measurable _)

def sourceBiasedRealMeasure (j : ℕ) (r : SourceCoordinate → Bool) : Measure SourceSamplingPair :=
  (sourceBiasedLaw j).map (sourceBiasedPair r)

instance sourceBiasedRealMeasure_probability (j : ℕ) (r : SourceCoordinate → Bool) :
    IsProbabilityMeasure (sourceBiasedRealMeasure j r) :=
  inferInstanceAs (IsProbabilityMeasure ((sourceBiasedLaw j).map (sourceBiasedPair r)))

def sourceBiasedTorusMeasure (j : ℕ) (r : SourceCoordinate → Bool) : FiniteMeasure SourceSamplingTorus :=
  ⟨(sourceBiasedRealMeasure j r).map sourceSamplingTorusMap,by infer_instance⟩

theorem sourceBiasedRealMeasure_marginal (j : ℕ) (r : SourceCoordinate → Bool) (b : Bool) :
    (sourceBiasedRealMeasure j r).map (sourceSamplingEndpoint b) =
      (sourceBiasedLaw j).map (sourceBiasedEndpoint (if b then r else fun _ => false)) := by
  rw [sourceBiasedRealMeasure,Measure.map_map (sourceSamplingEndpoint_measurable b)
    (sourceBiasedPair_measurable r)]
  cases b <;> rfl

/-- A nonnegative measurable version of each actual marginal density. -/
theorem sourceBiasedEndpoint_density (j : ℕ) (r : SourceCoordinate → Bool) :
    ∃ g : (SourceCoordinate → ℝ) → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      MemLp g 2 sourceSamplingHaar ∧
      (sourceBiasedLaw j).map (sourceBiasedEndpoint r) =
        sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      (∫ x, g x^2 ∂sourceSamplingHaar) ≤ Real.exp (20*(2*(∑' s,sourceKappa s^2)+1)) := by
  obtain ⟨f,hf,hf0,hfC,hfm⟩ := stagedCoupling_endpoint_L2_density j r
  let g := fun x => max (hf.aestronglyMeasurable.mk f x) 0
  have hg : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const
  have he : f =ᵐ[sourceSamplingHaar] g := by
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk,hf0] with x hx h0
    simp only [g,← hx,max_eq_left h0]
  refine ⟨g,hg,fun _ => le_max_right _ _,(memLp_congr_ae he).mp hf,?_,?_⟩
  · exact hfm.trans (withDensity_congr_ae (he.fun_comp ENNReal.ofReal))
  · exact (integral_congr_ae (he.mono fun x hx => congrArg (fun t : ℝ => t^2) hx)).symm.trans_le hfC

/-- Both mixed torus marginals have the same actual uniform L2 bound. -/
theorem sourceBiasedTorusMeasure_density (j : ℕ) (r : SourceCoordinate → Bool) (b : Bool) :
    ∃ g : SourceTorus → ℝ, Measurable g ∧ (∀ z, 0 ≤ g z) ∧
      MemLp g 2 sourceTorusHaar ∧
      (sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus).map (sourceTorusEndpoint b) =
        sourceTorusHaar.withDensity (fun z => ENNReal.ofReal (g z)) ∧
      (∫ z, g z^2 ∂sourceTorusHaar) ≤ Real.exp (20*(2*(∑' s,sourceKappa s^2)+1)) := by
  obtain ⟨f,hf,hf0,hflp,hfm,hfC⟩ := sourceBiasedEndpoint_density j (if b then r else fun _ => false)
  have hm : (sourceBiasedRealMeasure j r).map (sourceSamplingEndpoint b) =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (f x)) :=
    (sourceBiasedRealMeasure_marginal j r b).trans hfm
  refine ⟨f ∘ sourceTorusRepresentative,hf.comp sourceTorusRepresentative_preserving.measurable,
    fun z => hf0 _,hflp.comp_measurePreserving sourceTorusRepresentative_preserving,
    sourceSamplingTorus_marginal_transport _ b f hf hm,?_⟩
  have he : (∫ z, (f (sourceTorusRepresentative z))^2 ∂sourceTorusHaar) =
      ∫ x, f x^2 ∂sourceSamplingHaar := by
    rw [← sourceTorusRepresentative_preserving.map_eq]
    exact (integral_map sourceTorusRepresentative_preserving.measurable.aemeasurable
      (hf.pow_const 2).aestronglyMeasurable).symm
  exact he.trans_le hfC

/-- Every endpoint of every mixed-prefix or full biased law belongs to any
prescribed Haar-conull Borel set. -/
theorem sourceBiasedTorusMeasure_marginal_ac (j : ℕ) (r : SourceCoordinate → Bool) (b : Bool) :
    (sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus).map (sourceTorusEndpoint b) ≪ sourceTorusHaar := by
  obtain ⟨g,_,_,_,hm,_⟩ := sourceBiasedTorusMeasure_density j r b
  rw [hm]
  exact withDensity_absolutelyContinuous _ _

end
end FiniteFactor

end OAI
