import Mathlib

namespace OAI

/-! Endpoint-preserving restrictions and homotopies inside a simply connected
subspace. Used to turn coordinate-star homotopies into actual path homotopies. -/
noncomputable section

open Set
namespace HyperbolicObstruction.PathInSet
variable {X : Type*} [TopologicalSpace X] {x y : X} (s : Set X)

def restrict (p : Path x y) (hx : x ∈ s) (hy : y ∈ s) (hp : ∀ t, p t ∈ s) :
    Path (⟨x,hx⟩ : s) ⟨y,hy⟩ where
  toFun t := ⟨p t,hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] lemma restrict_map (p : Path x y) (hx : x ∈ s) (hy : y ∈ s) (hp : ∀ t, p t ∈ s) :
    (restrict s p hx hy hp).map continuous_subtype_val = p := by ext; rfl

lemma homotopic [SimplyConnectedSpace s] (p q : Path x y)
    (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) : p.Homotopic q := by
  have hx : x ∈ s := p.source ▸ hp 0
  have hy : y ∈ s := p.target ▸ hp 1
  have hh := SimplyConnectedSpace.paths_homotopic
    (restrict s p hx hy hp) (restrict s q hx hy hq)
  simpa using hh.map ⟨Subtype.val,continuous_subtype_val⟩

end HyperbolicObstruction.PathInSet
end

end OAI
