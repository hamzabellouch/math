import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateRegularReplacement

namespace OAI

/-! Germs of a Euclidean representative pull back to the original map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M]
variable {V : Type*}

theorem coordinate_model_germ (c : OpenPartialHomeomorph M Base)
    {f : M → V} {φ : Base → V} {O : Set Base} (hO : IsOpen O)
    (hmatch : EqOn φ (f ∘ c.symm) O) {x : M} (hx : x ∈ c.source)
    (hcx : c x ∈ O) : φ ∘ c =ᶠ[𝓝 x] f := by
  filter_upwards [c.open_source.mem_nhds hx,
    (c.continuousAt hx).preimage_mem_nhds (hO.mem_nhds hcx)] with y hy hyO
  have he := hmatch hyO
  change φ (c y) = f (c.symm (c y)) at he
  simpa only [Function.comp_apply,c.left_inv hy] using he

theorem coordinate_replacement_germ (c : OpenPartialHomeomorph M Base)
    {F G : Base → V} {x : M} (hx : x ∈ c.source)
    (he : F =ᶠ[𝓝 (c x)] G) : F ∘ c =ᶠ[𝓝 x] G ∘ c :=
  he.comp_tendsto (c.continuousAt hx).tendsto

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
