import Mathlib.Topology.Separation.Hausdorff

namespace OAI

/-! A compact map with a singleton fiber detects convergence at that
fiber. This extends lifted double arcs to their diagonal endpoints. -/
noncomputable section
open Set Filter Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y A : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y]

theorem tendsto_of_comp_singleton_fiber {f : X → Y} (hf : Continuous f) {x : X}
    (hfiber : ∀ z, f z = f x → z = x) {l : Filter A} {g : A → X}
    (h : Tendsto (f ∘ g) l (𝓝 (f x))) : Tendsto g l (𝓝 x) := by
  apply tendsto_nhds.mpr
  intro U hU hxU
  have hclosed : IsClosed (f '' Uᶜ) := (hU.isClosed_compl.isCompact.image hf).isClosed
  have hx : f x ∈ (f '' Uᶜ)ᶜ := by
    rintro ⟨z,hz,he⟩
    exact hz ((hfiber z he) ▸ hxU)
  have hevent := h (hclosed.isOpen_compl.mem_nhds hx)
  filter_upwards [hevent] with a ha
  by_contra hn
  exact ha ⟨g a,hn,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
