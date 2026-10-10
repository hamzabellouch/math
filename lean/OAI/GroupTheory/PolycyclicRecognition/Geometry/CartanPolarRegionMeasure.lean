import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedPolarRegions
import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientSectionIndependence

namespace OAI

/-! # A single target Haar normalization for all concentrated probes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (C : Set (H →ₗ[ℝ] ℝ)) (D : M.MeasuredCone F C)

/-- Every adapted target section gives exactly the same measure, not just
another scalar multiple of Haar measure. -/
theorem MeasuredCone.sectionMeasure_eq
    (σ τ : ContinuousMap D.Q.carrier F.N.carrier)
    (hσ : ∀ q, D.maps.quotient (σ q) = q)
    (hτ : ∀ q, D.maps.quotient (τ q) = q) :
    D.sectionMeasure M F C σ hσ = D.sectionMeasure M F C τ hτ := by
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup D.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.Q.modelSpace)) ⊤
  let bQ := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)).map
    D.Q.equiv.toLinearEquiv
  let coordQ := bQ.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartQ
  let : SecondCountableTopology D.Q.carrier := coordQ.symm.secondCountableTopology
  let : LocallyCompactSpace D.Q.carrier := coordQ.symm.isOpenEmbedding.locallyCompactSpace
  let bI := (finBasis ℝ (M.coneWordIdeal C)).map D.I.equiv.toLinearEquiv
  let coordI := bI.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartI
  let ke := kernelRealization D.maps.quotient D.maps.inclusion
    D.maps.inclusion_closed D.maps.inclusion_range
  let : SecondCountableTopology D.maps.quotient.ker :=
    (coordI.trans ke.toHomeomorph).symm.secondCountableTopology
  let : LocallyCompactSpace D.maps.quotient.ker :=
    (coordI.trans ke.toHomeomorph).symm.isOpenEmbedding.locallyCompactSpace
  let : D.measures.measureQ.IsHaarMeasure := D.measures.haarQ
  let : (D.kernelMeasure M F C).IsHaarMeasure := D.measures.haarKernel
  let : (D.kernelMeasure M F C).IsMulRightInvariant := D.measures.kernel_rightInvariant
  exact quotientSection_product_independent D.maps.quotient D.maps.quotient_continuous
    σ τ hσ hτ D.measures.measureQ (D.kernelMeasure M F C)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [IsTopologicalGroup F.N.carrier]

/-- Instantiate the published polar-region construction with twice the
concentration error and retain the fixed original target Haar measure.
The region threshold was chosen before the concentration error or its
path constant. -/
theorem MeasuredCone.fixed_polar_region_factory
    (K : ProperCone ℝ (StrongDual ℝ W)) (A : W →ₗ[ℝ] W) (ε : ℝ) (w : W)
    (height : G →* Multiplicative W)
    (act : G →* Equiv.Perm D.Q.carrier)
    (ν : Measure F.D.carrier) (cell : Set (F.N.carrier × F.D.carrier))
    (scale : ℕ → ℝ) (P₂ δ δ₀ : ℝ) (hδ : 0 < δ) (hδ₀ : δ ≤ δ₀)
    (regions : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
      ∃ R : MeasuredProbeRegions D.maps.quotient D.measures.measureQ
        (D.kernelMeasure M F C) ν scale P₂,
        ∀ δ' : ℝ, 0 < δ' → δ' ≤ δ₀ →
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          height cell (A '' normalizedPolarTemplates K ε 0)
          (A '' normalizedPolarTemplates K ε 2) η Cp Clog δ' n) :
    ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp : ℝ, 0 ≤ Cp →
      ∃ R : MeasuredProbeRegions D.maps.quotient D.measures.measureQ
        (D.kernelMeasure M F C) ν scale P₂,
        D.sectionMeasure M F C D.maps.sectionMap D.maps.section_rightInverse =
          Measure.map (quotientSectionHomeomorph D.maps.quotient
            D.maps.quotient_continuous R.sectionMap R.section_rightInverse).symm
            (D.measures.measureQ.prod (D.kernelMeasure M F C)) ∧
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          height cell
          ((fun z => A (z - w)) '' polarSamplingTemplates K ε w 0)
          ((fun z => A (z - w)) '' polarSamplingTemplates K ε w 2)
          (fun n => 2 * η n) Cp Cp δ n := by
  intro η hη0 hη Cp hCp
  have htwo : Tendsto (fun n => 2 * η n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hη
  obtain ⟨R, hR⟩ := regions (fun n => 2 * η n)
    (fun n => mul_nonneg (by norm_num) (hη0 n)) htwo Cp Cp hCp hCp
  refine ⟨R, ?_, ?_⟩
  · exact D.sectionMeasure_eq M F C D.maps.sectionMap R.sectionMap
      D.maps.section_rightInverse R.section_rightInverse
  · simpa only [recentered_polarSamplingTemplates] using hR δ hδ hδ₀

end PolycyclicRecognition.CartanWordModel

end

end OAI
