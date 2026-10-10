import Mathlib
import OAI.Geometry.HyperbolicGroups.MappedPicture
import OAI.Geometry.HyperbolicGroups.PairingForest
import OAI.Geometry.HyperbolicGroups.SubpairingTree
import OAI.Geometry.HyperbolicGroups.PictureCotreeColor

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

include hq in
omit [DecidableEq D] [Fintype D] [Nonempty D] in
lemma complement_boundary_eq : M.face * (q*M.edge) = M.vertex*q := by
  have hcomm : q*M.edge = M.edge*q := by
    ext x; exact M.subpairing_edge q hq x
  have hface : M.face = M.vertex*M.edge := by
    rw [vertex,mul_assoc,M.edge_sq,mul_one]
  rw [hface]
  calc
    _ = M.vertex * (M.edge*q) * M.edge := by simp only [mul_assoc]
    _ = M.vertex * (q*M.edge) * M.edge := by rw [← hcomm]
    _ = (M.vertex*q) * (M.edge*M.edge) := by simp only [mul_assoc]
    _ = M.vertex*q := by rw [M.edge_sq,mul_one]

/-- The complement of ANY literal spanning-tree subpairing is a dual tree,
not just the particular Kruskal forest supplied by tree_cotree. This is
needed when the primal tree is chosen for a radius bound. -/
theorem cotree_isTree (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1) : (M.cotreeGraph q hq).IsTree := by
  have hconn : M.components = ⊤ := top_unique (hspan ▸ M.subpairing_components_le q hq)
  let r := q*M.edge
  have hr := M.complement_subpairing q hq
  have hrb : cycles (M.face*r) = 1 := by
    rw [show M.face*r = M.vertex*q from M.complement_boundary_eq q hq,hboundary]
  have hqE := M.subpairing_euler q hq hG
  rw [hspan,card_quotient_top_one,hboundary] at hqE
  have hrE := M.dual.subpairing_euler r hr (M.dual_genusZero hG)
  rw [M.dual_vertex,hrb] at hrE
  have hE := hG
  change cycles M.vertex + cycles M.face - (Fintype.card D : ℤ)/2 =
    2*(Nat.card (Quotient M.components) : ℤ) at hE
  rw [hconn,card_quotient_top_one] at hE
  have hsupp : q.support.card + r.support.card = Fintype.card D := by
    rw [show r.support = Finset.univ \ q.support from M.complement_support q hq,
      Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
    have hh := Finset.card_le_card (Finset.subset_univ q.support)
    rw [Finset.card_univ] at hh
    omega
  obtain ⟨l,_,hl,_⟩ := involution_pairs q (M.subpairing_sq q hq)
  obtain ⟨t,_,ht,_⟩ := involution_pairs r (M.subpairing_sq r hr)
  have hc : Nat.card (Quotient (SameCycle.setoid M.face ⊔ SameCycle.setoid r)) = 1 := by omega
  have hds : SameCycle.setoid M.face ⊔ SameCycle.setoid r = ⊤ :=
    setoid_eq_of_card_eq le_top (hc.trans card_quotient_top_one.symm)
  apply M.dual.subpairing_isTree (M.dual_genusZero hG) r hr
  · simpa only [M.dual_vertex] using hds
  · simpa only [M.dual_vertex] using hrb

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
