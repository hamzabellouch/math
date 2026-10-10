import OAI.Geometry.SurfaceImmersion.Atlas.MatchedSubsetChart

namespace OAI

/-! The zero slice in a product is a copy of the line; this converts
submersion coordinates into charts on matched zero subsets. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [Zero E]

def zeroSliceLineHomeomorph : {z : E × ℝ // z.1 = 0} ≃ₜ ℝ where
  toFun := fun z => z.val.2
  invFun := fun t => ⟨(0,t),rfl⟩
  left_inv := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · exact z.property.symm
    · rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val.snd
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

theorem matched_zero_subset_line_chart (e : OpenPartialHomeomorph X (E × ℝ))
    (S : Set X) (p : X) (hp : p ∈ e.source) (hpS : p ∈ S)
    (hmatch : ∀ x ∈ e.source, x ∈ S ↔ (e x).1 = 0) :
    ∃ c : OpenPartialHomeomorph S ℝ, (⟨p,hpS⟩ : S) ∈ c.source := by
  obtain ⟨a,ha,_,_,_,_⟩ := matched_subset_chart e S {z | z.1 = 0} p hp hpS hmatch
  let h := (zeroSliceLineHomeomorph (E := E)).toOpenPartialHomeomorph
  refine ⟨a.trans h,?_⟩
  change (⟨p,hpS⟩ : S) ∈ a.source ∧ a ⟨p,hpS⟩ ∈ h.source
  exact ⟨ha,mem_univ _⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
