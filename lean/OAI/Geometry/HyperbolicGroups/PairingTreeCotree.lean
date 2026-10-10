import Mathlib
import OAI.Geometry.HyperbolicGroups.MappedPicture
import OAI.Geometry.HyperbolicGroups.PairingForest
import OAI.Geometry.HyperbolicGroups.PictureDual

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap
variable (M : PictureMap D)

omit [DecidableEq D] in
lemma subpairing_components_le (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x) :
    SameCycle.setoid M.vertex ⊔ SameCycle.setoid q ≤ M.components := by
  apply sup_le M.vertex_le_components
  apply sameCycle_le_of_apply
  intro x
  rcases hq x with hx | hx
  · rw [hx]
  · rw [hx]; exact M.edge_le_components SameCycle.rfl.apply_right

/-- Actual tree--cotree decomposition of each component of a genus-zero
ribbon graph. Both permutations pair subsets of the original edge copies.
Their supports are complementary, neither collapses parallel edges, and
both spanning forests have exactly one boundary cycle per component. -/
theorem tree_cotree (hG : M.GenusZero) : ∃ q : Perm D,
    (∀ x, q x = x ∨ q x = M.edge x) ∧
    SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = M.components ∧
    cycles (M.vertex * q) = (Nat.card (Quotient M.components) : ℤ) ∧
    SameCycle.setoid M.face ⊔ SameCycle.setoid (q * M.edge) = M.components ∧
    cycles (M.face * (q * M.edge)) = (Nat.card (Quotient M.components) : ℤ) := by
  obtain ⟨q,hq,hspan,hboundary⟩ := M.spanning_forest
  let r := q * M.edge
  have hr := M.complement_subpairing q hq
  have hcomp : q * M.edge = M.edge * q := by
    ext x; exact M.subpairing_edge q hq x
  have hface : M.face = M.vertex * M.edge := by
    rw [vertex,mul_assoc,M.edge_sq,mul_one]
  have hdualboundary : M.face * r = M.vertex * q := by
    rw [hface]
    change (M.vertex * M.edge) * (q * M.edge) = M.vertex * q
    calc
      _ = M.vertex * (M.edge * q) * M.edge := by simp only [mul_assoc]
      _ = M.vertex * (q * M.edge) * M.edge := by rw [← hcomp]
      _ = (M.vertex * q) * (M.edge * M.edge) := by simp only [mul_assoc]
      _ = M.vertex * q := by rw [M.edge_sq,mul_one]
  have hqE := M.subpairing_euler q hq hG
  rw [hspan,hboundary] at hqE
  have hrE := M.dual.subpairing_euler r hr (M.dual_genusZero hG)
  rw [M.dual_vertex,hdualboundary,hboundary] at hrE
  have hsupp : q.support.card + r.support.card = Fintype.card D := by
    rw [show r.support = Finset.univ \ q.support from M.complement_support q hq,
      Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
    have hle := Finset.card_le_card (Finset.subset_univ q.support)
    rw [Finset.card_univ] at hle
    omega
  obtain ⟨l,_,hl,_⟩ := involution_pairs q (M.subpairing_sq q hq)
  obtain ⟨t,_,ht,_⟩ := involution_pairs r (M.subpairing_sq r hr)
  have hE := hG
  change cycles M.vertex + cycles M.face - (Fintype.card D : ℤ) / 2 = _ at hE
  have hcard : Nat.card (Quotient (SameCycle.setoid M.face ⊔ SameCycle.setoid r)) =
      Nat.card (Quotient M.components) := by omega
  have hle : SameCycle.setoid M.face ⊔ SameCycle.setoid r ≤ M.components := by
    have hh := M.dual.subpairing_components_le r hr
    simpa only [M.dual_vertex,M.dual_components] using hh
  refine ⟨q,hq,hspan,hboundary,setoid_eq_of_card_eq hle hcard,?_⟩
  change cycles (M.face * r) = _
  rw [hdualboundary,hboundary]

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
