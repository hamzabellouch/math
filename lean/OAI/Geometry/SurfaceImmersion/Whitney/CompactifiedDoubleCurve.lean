import OAI.Geometry.SurfaceImmersion.Whitney.UnorderedSurfacePairs
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapDiagonalClosure

namespace OAI

/-! Compactifying distinct unordered double pairs retains precisely the
prepared crosscaps on the diagonal. -/
noncomputable section
open Set Topology Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M]

def compactifiedDoubleCurve (f : M → ProjectionTarget 3) : Set (UnorderedSurfacePairs M) :=
  unorderedPair '' closure (surfaceDoublePairs f)

lemma compactifiedDoubleCurve_diagonal (f : M → ProjectionTarget 3) (p : M) :
    unorderedPair (p,p) ∈ compactifiedDoubleCurve f ↔ (p,p) ∈ closure (surfaceDoublePairs f) := by
  constructor
  · rintro ⟨z,hz,he⟩
    have hzp : z = (p,p) := by
      rcases unorderedPair_eq.mp he with he | he
      · exact he
      · simpa only [Prod.swap_prod_mk] using he
    rwa [← hzp]
  · intro hp
    exact ⟨(p,p),hp,rfl⟩

lemma compactifiedDoubleCurve_compact [CompactSpace M] (f : M → ProjectionTarget 3) :
    IsCompact (compactifiedDoubleCurve f) :=
  isClosed_closure.isCompact.image unorderedPair_continuous

lemma compactifiedDoubleCurve_eq_closure [CompactSpace M] [T2Space M]
    (f : M → ProjectionTarget 3) :
    compactifiedDoubleCurve f = closure (unorderedPair '' surfaceDoublePairs f) := by
  apply Set.Subset.antisymm
  · rintro z ⟨x,hx,rfl⟩
    exact mem_closure_image unorderedPair_continuous.continuousAt hx
  · exact closure_minimal (Set.image_mono subset_closure) (compactifiedDoubleCurve_compact f).isClosed

variable [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

lemma compactifiedDoubleCurve_finite_diagonal {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfinite : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite) :
    (compactifiedDoubleCurve f ∩ Set.range (fun p : M => unorderedPair (p,p))).Finite := by
  apply (hfinite.image (fun p : M => unorderedPair (p,p))).subset
  rintro z ⟨hz,⟨p,rfl⟩⟩
  exact ⟨p,doublePairs_closure_diagonal_singular hf p ((compactifiedDoubleCurve_diagonal f p).mp hz),rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
