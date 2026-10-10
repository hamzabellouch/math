import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonFacialStars
open Set Topology

variable {X D V : Type*} [TopologicalSpace X] [Finite D]

theorem interior_union_at (C : D → Set X) (hC : ∀ d,IsClosed (C d))
    (hcover : ∀ x,∃ d,x∈C d) (S : Set D) {x : X}
    (hx : ∀ d,x∈C d → d∈S) : x∈interior (⋃ d∈S,C d) := by
  let B := ⋃ d∈Sᶜ,C d
  have hB : IsClosed B := isClosed_iUnion_of_finite fun d =>
    isClosed_iUnion_of_finite fun _ => hC d
  have hxB : x∈Bᶜ := by
    intro hxB
    obtain ⟨d,hd,hxd⟩ := mem_iUnion₂.mp hxB
    exact hd (hx d hxd)
  apply mem_interior.mpr
  refine ⟨Bᶜ,?_,hB.isOpen_compl,hxB⟩
  intro y hy
  obtain ⟨d,hd⟩ := hcover y
  have hdS : d∈S := by
    by_contra hh
    exact hy (mem_iUnion₂.mpr ⟨d,hh,hd⟩)
  exact mem_iUnion₂.mpr ⟨d,hdS,hd⟩
end CannonFacialStars

end
end
end
end

end OAI
