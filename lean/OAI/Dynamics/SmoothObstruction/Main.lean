import OAI.Dynamics.SmoothObstruction.Counting
import OAI.Dynamics.SmoothObstruction.BoundaryDensity
import OAI.Dynamics.SmoothObstruction.Obstruction

namespace OAI

section

namespace SmoothObstruction
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {d : ℕ} {M : Type} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]

theorem euclidean_switching [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    [IsManifold (𝓡 d) ∞ M]
    (μ : ProbabilityMeasure M) (hμ : SmoothPositiveDensity (𝓡 d) (μ : Measure M))
    (S : Diffeomorph (𝓡 d) (𝓡 d) M M ∞)
    (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M)) :
    SmoothSwitching (μ : Measure M) S S.symm := by
  have hr : range (𝓡 d)=univ := by ext x; simp
  apply ManifoldCoordinates.switching_from_gauges (𝓡 d) (by rw [hr]; exact isClosed_univ) μ hμ S hS
  intro ι inst a K hK hKU
  refine ⟨0,le_rfl,?_⟩
  intro r hr₀
  refine ⟨∅,MeasurableSet.empty,by simp,?_⟩
  intro i x hx hxW
  rw [hr,interior_univ]
  exact subset_univ _

theorem halfspace_switching [NeZero d] [ChartedSpace (EuclideanHalfSpace d) M]
    [IsManifold (𝓡∂ d) ∞ M]
    (μ : ProbabilityMeasure M) (hμ : SmoothPositiveDensity (𝓡∂ d) (μ : Measure M))
    (S : Diffeomorph (𝓡∂ d) (𝓡∂ d) M M ∞)
    (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M)) :
    SmoothSwitching (μ : Measure M) S S.symm := by
  have hr : IsClosed (range (𝓡∂ d)) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact isClosed_le continuous_const (by fun_prop)
  apply ManifoldCoordinates.switching_from_gauges (𝓡∂ d) hr μ hμ S hS
  intro ι inst a K hK hKU
  obtain ⟨C,hC,hcol⟩ := ChartDensity.global_halfspace_collar (μ : Measure M) hμ a K hK hKU
  exact ⟨C,hC.le,hcol⟩
end SmoothObstruction

namespace SmoothObstruction
open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff
open WordHierarchy

/-- No closed smooth positive-density model in any finite dimension. The
compatible metric used in the switching proof is chosen from the given topology;
no metric or orientability hypothesis is imposed on the model. -/
theorem no_euclidean_model (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (d : ℕ) :
    ¬ HasModelWith μ T (𝓡 d) := by
  classical
  rintro ⟨M,top,meas,borel,t2,ct,compact,chart,manifold,ν,prob,S,hν,hS,hc⟩
  let : TopologicalSpace M := top
  let : MeasurableSpace M := meas
  let : BorelSpace M := borel
  let : T2Space M := t2
  let : SecondCountableTopology M := ct
  let : CompactSpace M := compact
  let : ChartedSpace (EuclideanSpace ℝ (Fin d)) M := chart
  let : IsManifold (𝓡 d) ∞ M := manifold
  let : IsProbabilityMeasure ν := prob
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let : Nonempty M := nonempty_of_isProbabilityMeasure ν
  have hswitch := euclidean_switching (⟨ν,prob⟩ : ProbabilityMeasure M) hν S hS
  have hSi : MeasurePreserving S.symm ν ν :=
    MeasurePreserving.symm S.toHomeomorph.toMeasurableEquiv hS
  obtain ⟨r,hr,B,hB,hBc,hBf,hBi,hforward,hinverse⟩ :=
    ConullTransport.from_conjugate_bilateral μ ν T.toEquiv S.toEquiv hc
      (Classical.choice (nonempty_of_isProbabilityMeasure μ))
  exact no_switching μ hT ν S.toEquiv hS hSi r hr B hB hBc hBi hforward hswitch

/-- The same obstruction for smooth boundary manifolds, with their genuine
half-space chart densities. No orientability assumption is introduced. -/
theorem no_halfspace_model (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (d : ℕ) [NeZero d] :
    ¬ HasModelWith μ T (𝓡∂ d) := by
  classical
  rintro ⟨M,top,meas,borel,t2,ct,compact,chart,manifold,ν,prob,S,hν,hS,hc⟩
  let : TopologicalSpace M := top
  let : MeasurableSpace M := meas
  let : BorelSpace M := borel
  let : T2Space M := t2
  let : SecondCountableTopology M := ct
  let : CompactSpace M := compact
  let : ChartedSpace (EuclideanHalfSpace d) M := chart
  let : IsManifold (𝓡∂ d) ∞ M := manifold
  let : IsProbabilityMeasure ν := prob
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let : Nonempty M := nonempty_of_isProbabilityMeasure ν
  have hswitch := halfspace_switching (⟨ν,prob⟩ : ProbabilityMeasure M) hν S hS
  have hSi : MeasurePreserving S.symm ν ν :=
    MeasurePreserving.symm S.toHomeomorph.toMeasurableEquiv hS
  obtain ⟨r,hr,B,hB,hBc,hBf,hBi,hforward,hinverse⟩ :=
    ConullTransport.from_conjugate_bilateral μ ν T.toEquiv S.toEquiv hc
      (Classical.choice (nonempty_of_isProbabilityMeasure μ))
  exact no_switching μ hT ν S.toEquiv hS hSi r hr B hB hBc hBi hforward hswitch

/-- Both sides of the phase-extension shift have the original product
sigma-algebra measurability, independent of any choice of compatible metrics. -/
lemma measurable_word_inverse : Measurable (T.symm : Extension → Extension) := by
  apply Measurable.subtype_mk
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun t =>
      ((measurable_pi_apply (t-1)).comp measurable_fst).comp measurable_subtype_coe)
  · exact measurable_pi_iff.mpr (fun i =>
      (measurable_of_countable (fun a : ZMod (WordParameters.length 40000 i) => a-1)).comp
        (measurable_phase i))

noncomputable def wordMeasurableEquiv : Extension ≃ᵐ Extension where
  toEquiv := T.toEquiv
  measurable_toFun := measurable_T
  measurable_invFun := measurable_word_inverse

/-- An ergodic invertible finite-KS-entropy transformation of a standard
nonatomic probability space, with no compact finite-dimensional smooth
strictly-positive-density model even modulo invariant null sets. -/
theorem main :
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (_ : IsProbabilityMeasure μ) (T : X ≃ᵐ X),
      StandardNonatomic μ ∧ Ergodic T μ ∧ FiniteKSEntropy μ T ∧
        ¬ HasSmoothPositiveVolumeModel μ T := by
  classical
  obtain ⟨μ,hstd,herg,hent⟩ := actual_system
  refine ⟨Extension,inferInstance,(μ : Measure Extension),inferInstance,
    wordMeasurableEquiv,hstd,herg,hent,?_⟩
  rintro (⟨d,hmodel⟩ | ⟨d,hd,hmodel⟩)
  · exact no_euclidean_model (μ : Measure Extension) herg.toMeasurePreserving d hmodel
  · let : NeZero d := hd
    exact no_halfspace_model (μ : Measure Extension) herg.toMeasurePreserving d hmodel
end SmoothObstruction

end

end OAI
