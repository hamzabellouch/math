import OAI.Analysis.CircleDomains.Probability.PathIntersectionMeasure
import OAI.Analysis.CircleDomains.Transfer.TransportedMeanIndex
import OAI.Analysis.CircleDomains.Selection.LiftedMeanContinuity

namespace OAI

/-! The actual local branch of the averaged ray index is paid for by
the finite expected intersection measure of a prior level union. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem lifted_mean_index_arc_payment
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {H V : Set X} (hH : IsClosed H)
    (hfinite : (∫⁻ γ, pathImageCount H γ
      ∂((η.map Subtype.val : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞)
    (Ψ : X → ℂ) (hΨ : ContinuousOn Ψ V)
    (hpos : ∀ x ∈ V, 0 ≤ (Ψ x).im)
    (hproj : ∀ x ∈ V, diskRayProjection (Ψ x) = F x)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ V)) (hinj : InjOn F V)
    (α : C(PathTime, X)) (hα : Injective α)
    (hαV : range α ⊆ V) (hαH : range α ⊆ H) :
    ENNReal.ofReal
      |liftedMeanGeometricIndex hsch K hKS (η.map f) id (Ψ (α 1)) -
        liftedMeanGeometricIndex hsch K hKS (η.map f) id (Ψ (α 0))| ≤
      meanPathIntersectionMeasure H
        ((η.map Subtype.val : ProbabilityMeasure C(PathTime, X)) : Measure _) (range α) := by
  let δ : C(PathTime, ℂ) :=
    ⟨Ψ ∘ α, hΨ.comp_continuous α.continuous (fun t => hαV (mem_range_self t))⟩
  have hδ : ∀ t, 0 ≤ (δ t).im := fun t => hpos (α t) (hαV (mem_range_self t))
  have hδproj : ∀ t, diskRayProjection (δ t) = F (α t) :=
    fun t => hproj (α t) (hαV (mem_range_self t))
  have hδinj : Injective (diskRayProjection ∘ δ) := by
    intro t u h
    apply hα
    apply hinj (hαV (mem_range_self t)) (hαV (mem_range_self u))
    exact (hδproj t).symm.trans (h.trans (hδproj u))
  have hp := meanGeometricIndex_mapped_difference_le_intersections hsch hsep A K hK
    hKS η F f hf hmap α δ hδ hδproj hδinj
    (fun γ => (hF γ).mono (union_subset_union_right _ hαV))
  have hν : meanPathIntersectionMeasure H
      ((η.map Subtype.val : ProbabilityMeasure C(PathTime, X)) : Measure _) (range α) =
      ∫⁻ γ : A, pathImageCount (range α) γ.val ∂(η : Measure A) := by
    rw [meanPathIntersectionMeasure_apply_subset H hH _ hfinite (range α)
      (isCompact_range α.continuous).isClosed.measurableSet hαH,
      ProbabilityMeasure.toMeasure_map]
    exact lintegral_map (measurable_pathImageCount
      (isCompact_range α.continuous).isClosed) measurable_subtype_coe
  rw [hν, liftedMeanGeometricIndex_eq hsch K hKS (η.map f) id (Ψ (α 1)) (hδ 1),
    liftedMeanGeometricIndex_eq hsch K hKS (η.map f) id (Ψ (α 0)) (hδ 0)]
  exact hp

end CircleDomainRigidity

end

end OAI
