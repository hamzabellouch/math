import OAI.Geometry.SurfaceImmersion.Atlas.MatchedSubsetChart

namespace OAI

/-! An embedding whose image contains a neighborhood supplies a local
inverse chart on that neighborhood. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem embedding_neighborhood_chart (f : X → Y) (hf : IsEmbedding f) (p : X)
    {V : Set Y} (hV : IsOpen V) (hpV : f p ∈ V) (hsub : V ⊆ range f) :
    ∃ c : OpenPartialHomeomorph Y X, f p ∈ c.source ∧ c (f p) = p := by
  let : Nonempty X := ⟨p⟩
  let a := hf.toPartialHomeomorph f
  have hback (y : Y) (hy : y ∈ V) : f (a.symm y) = y :=
    hf.toPartialHomeomorph_right_inv f (hsub hy)
  let e : OpenPartialHomeomorph X Y := {
    toFun := f
    invFun := a.symm
    source := f ⁻¹' V
    target := V
    map_source' := fun _ hx => hx
    map_target' := by
      intro y hy
      change f (a.symm y) ∈ V
      rwa [hback y hy]
    left_inv' := fun x _ => hf.toPartialHomeomorph_left_inv f
    right_inv' := hback
    continuousOn_toFun := hf.continuous.continuousOn
    continuousOn_invFun := by
      apply a.continuousOn_symm.mono
      intro y hy
      change y ∈ f '' univ
      simpa only [image_univ] using hsub hy
    open_source := hV.preimage hf.continuous
    open_target := hV }
  exact ⟨e.symm,hpV,hf.toPartialHomeomorph_left_inv f⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
