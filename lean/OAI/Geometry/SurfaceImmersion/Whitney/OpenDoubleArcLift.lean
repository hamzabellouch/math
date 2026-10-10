import OAI.Geometry.SurfaceImmersion.Geometry.UnorderedPairCovering
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-! Lift an interior double arc to a continuous ordered pair. -/
noncomputable section
open Set Topology unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]

theorem open_double_arc_lift (γ : C(I, UnorderedSurfacePairs M))
    (hγ : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∈ unorderedDistinctPairs M) :
    ∃ F : C(Ioo (0:ℝ) 1, M × M), ∀ t,
      unorderedPair (F t) = γ ⟨t.val,t.property.1.le,t.property.2.le⟩ := by
  let A := Ioo (0:ℝ) 1
  let a : A := ⟨1/2,by constructor <;> norm_num⟩
  let : ContractibleSpace A := (convex_Ioo (0:ℝ) 1).contractibleSpace ⟨a.val,a.property⟩
  let : LocallyPathConnectedSpace A := isOpen_Ioo.locallyPathConnectedSpace
  let f : C(A,UnorderedSurfacePairs M) := ⟨fun t => γ ⟨t.val,t.property.1.le,t.property.2.le⟩,
    γ.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  obtain ⟨e,he⟩ := Quotient.exists_rep (f a)
  have he' : unorderedPair e = f a := he
  obtain ⟨F,⟨_,hF⟩,_⟩ := unorderedPair_covering.existsUnique_continuousMap_lifts f he'
    (fun t => hγ _ t.property.1 t.property.2)
  exact ⟨F,fun t => congrFun hF t⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
