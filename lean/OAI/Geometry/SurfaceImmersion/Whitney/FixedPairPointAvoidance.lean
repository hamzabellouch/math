import OAI.Geometry.SurfaceImmersion.Whitney.FixedSurfacePairPatch
import OAI.Geometry.SurfaceImmersion.Whitney.SurfacePairPointAvoidance

namespace OAI

/-! The fixed cutoff patches also remove coincidences at prescribed finite points. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SurfacePairTranslationPatch

theorem regularize_avoiding_points {p q : M} (P : SurfacePairTranslationPatch p q)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (S T : Set M) (hS : S.Finite) (hT : T.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ProjectionTarget 3, ‖a‖ < ε ∧ ∀ x ∈ P.U, ∀ y ∈ P.V,
      surfaceTranslation f P.χ a x = surfaceTranslation f P.χ a y →
      x ∉ S ∧ y ∉ T ∧ Function.Surjective (surfacePairDerivative (surfaceTranslation f P.χ a) x y) := by
  obtain ⟨F,hF,heF⟩ := surface_compact_representative hf p isClosed_closure.isCompact P.sourceU
  obtain ⟨G,hG,heG⟩ := surface_compact_representative hf q isClosed_closure.isCompact P.sourceV
  exact surface_pair_patch_translation_avoiding_points p q hF hG P.openU P.openV
    (fun x hx => P.sourceU (subset_closure hx)) (fun y hy => P.sourceV (subset_closure hy))
    (heF.mono subset_closure) (heG.mono subset_closure) P.oneOn P.zeroOn S T hS hT hε

end SurfacePairTranslationPatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
