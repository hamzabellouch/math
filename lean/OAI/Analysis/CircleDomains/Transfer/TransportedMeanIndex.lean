import OAI.Analysis.CircleDomains.Selection.MeanIndexIntersections
import OAI.Analysis.CircleDomains.Topology.PathImageCountMap

namespace OAI

/-! The actual mean-index increment estimate in the original physical
coordinates. The Jordan map is used only through continuity and injectivity. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
 theorem meanGeometricIndex_mapped_difference_le_intersections
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (α : C(PathTime, X)) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hproj : ∀ t, diskRayProjection (δ t) = F (α t))
    (hinj : Injective (diskRayProjection ∘ δ))
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ range α)) :
    ENNReal.ofReal |meanGeometricIndex hsch K hKS (η.map f) ⟨δ 1, hδ 1⟩ -
      meanGeometricIndex hsch K hKS (η.map f) ⟨δ 0, hδ 0⟩| ≤
      ∫⁻ γ : A, pathImageCount (range α) γ.val ∂(η : Measure A) := by
  have hclosed : IsClosed (diskRayProjection '' range δ) :=
    ((isCompact_range δ.continuous).image continuous_diskRayProjection).isClosed
  have he : diskRayProjection '' range δ = F '' range α := by
    rw [← range_comp, ← range_comp]
    congr 1
    funext t
    exact hproj t
  apply (meanGeometricIndex_difference_le_intersections hsch hsep K hK hKS (η.map f)
    δ hδ hinj).trans
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map]
  · apply lintegral_mono
    intro γ
    change pathImageCount (diskRayProjection '' range δ) (f γ).val ≤
      pathImageCount (range α) γ.val
    rw [hmap γ, he]
    exact pathImageCount_map_le F γ.val (range α) (hF γ)
  · exact (measurable_pathImageCount hclosed).comp measurable_subtype_coe
  · exact hf

end CircleDomainRigidity

end

end OAI
