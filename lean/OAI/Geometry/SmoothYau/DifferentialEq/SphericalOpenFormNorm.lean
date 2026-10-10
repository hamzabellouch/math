import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ContinuousFamilyEventuallyTest
import OAI.Geometry.SmoothYau.Estimates.SphericalPinFormNorm
import OAI.Geometry.SmoothYau.Geometry.SourceRoundChartMetricUpper

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
namespace YauCounterexamples
local instance sphericalOpenFormNorm : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalOpenFormSpace : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
def sphericalPositiveSet (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) : Set SphericalTensor :=
  {H | chartTensorPositive g₀ sourcePole sphericalTensorSupport H}
abbrev SphericalPositiveTensor (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) := sphericalPositiveSet g₀
def sphericalTensorMetric (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (H : SphericalPositiveTensor g₀) : SmoothMetric (Euclidean 3) (Sphere 3) :=
  chartTensorMetric g₀ sourcePole sphericalTensorSupport
    ((sphere_chart_target sourcePole).symm ▸ subset_univ _) H.val H.property
lemma sphericalPositiveSet_isOpen (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) :
    IsOpen (sphericalPositiveSet g₀) :=
  isOpen_chartTensorPositive g₀ sourcePole sphericalTensorSupport
    ((sphere_chart_target sourcePole).symm ▸ subset_univ _)
lemma sphericalTensorOf_positive (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3))
    (he : sphericalExterior g₀ g (3/10)) : sphericalTensorOf g₀ g he ∈ sphericalPositiveSet g₀ :=
  chartTensorOfMetric_positive g₀ sourcePole sphericalTensorSupport (sphere_chart_target sourcePole)
    g (sphericalExterior_support le_rfl he)
lemma sphericalTensorMetric_of (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3))
    (he : sphericalExterior g₀ g (3/10)) :
    sphericalTensorMetric g₀ ⟨sphericalTensorOf g₀ g he,sphericalTensorOf_positive g₀ g he⟩=g :=
  chartTensorMetric_ofMetric g₀ sourcePole sphericalTensorSupport (sphere_chart_target sourcePole)
    g (sphericalExterior_support le_rfl he)
lemma sphericalPositive_zero (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) :
    (0 : SphericalTensor) ∈ sphericalPositiveSet g₀ := by
  simpa only [sphericalTensorOf_zero] using sphericalTensorOf_positive g₀ g₀ (fun _ _ => rfl)
lemma sphericalTensorMetric_zero (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) :
    sphericalTensorMetric g₀ ⟨0,sphericalPositive_zero g₀⟩=g₀ := by
  simpa only [sphericalTensorOf_zero] using sphericalTensorMetric_of g₀ g₀ (fun _ _ => rfl)
lemma sphericalTensorMetric_family (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (r : Sphere 3) (i j : CoordIndex (Euclidean 3)) :
    ContinuousSmoothFamilyOn
      (fun H y => metricCoefficients (sphericalTensorMetric g₀ H) r y i j)
      (chartAt (Euclidean 3) r).target :=
  family_chartTensorMetric g₀ sourcePole sphericalTensorSupport
    ((sphere_chart_target sourcePole).symm ▸ subset_univ _) Subtype.val
    (fun H => H.property) continuous_subtype_val r i j

def SphericalMetricGood (g : SmoothMetric (Euclidean 3) (Sphere 3)) : Prop :=
  g ∈ sphericalProfileMetricNeighborhood ∧
    ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
        ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2
lemma sphericalMetricGood_neighborhood (g₀ : SmoothMetric (Euclidean 3) (Sphere 3))
    (hg₀ : IsRound g₀) : IsSmoothNeighborhood g₀ {g | SphericalMetricGood g} :=
  IsSmoothNeighborhood.inter g₀ (sphericalProfileMetricNeighborhood_isNeighborhood g₀ hg₀)
    (spherical_coordinate_upper_neighborhood g₀ hg₀)

lemma exists_spherical_open_model (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (N : Set (SmoothMetric (Euclidean 3) (Sphere 3))) (hN : IsSmoothNeighborhood g₀ N) :
    ∃ O : Set SphericalTensor, IsOpen O ∧ 0 ∈ O ∧
      ∀ H ∈ O, ∃ hp : H ∈ sphericalPositiveSet g₀,
        sphericalTensorMetric g₀ ⟨H,hp⟩ ∈ N ∧ SphericalMetricGood (sphericalTensorMetric g₀ ⟨H,hp⟩) := by
  let z₀ : SphericalPositiveTensor g₀ := ⟨0,sphericalPositive_zero g₀⟩
  have htest : IsSmoothNeighborhood (sphericalTensorMetric g₀ z₀)
      (N ∩ {g | SphericalMetricGood g}) := by
    rw [show sphericalTensorMetric g₀ z₀=g₀ from sphericalTensorMetric_zero g₀]
    exact IsSmoothNeighborhood.inter g₀ hN (sphericalMetricGood_neighborhood g₀ hg₀)
  have hev := continuousFamily_eventually_neighborhood (sphericalTensorMetric g₀)
    (sphericalTensorMetric_family g₀) z₀ htest
  obtain ⟨V,hV,hVo,hzV⟩ := mem_nhds_iff.mp hev
  refine ⟨Subtype.val '' V,(sphericalPositiveSet_isOpen g₀).isOpenMap_subtype_val V hVo,
    ⟨z₀,hzV,rfl⟩,?_⟩
  rintro H ⟨z,hz,rfl⟩
  exact ⟨z.property,hV hz⟩
end YauCounterexamples
end

end OAI
