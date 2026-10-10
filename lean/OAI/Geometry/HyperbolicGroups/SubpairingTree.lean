import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.CycleCount
import OAI.Geometry.HyperbolicGroups.InvolutionPairs
import OAI.Geometry.HyperbolicGroups.PairingTreeCotree
import OAI.Geometry.HyperbolicGroups.PictureDual
import OAI.Geometry.HyperbolicGroups.PlanarSubpairing
import OAI.Geometry.HyperbolicGroups.SubpairingGraph

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]

omit [DecidableEq D] [Fintype D] in
lemma card_quotient_top_one : Nat.card (Quotient (⊤ : Setoid D)) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro a b
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact Quotient.sound trivial
  · exact ⟨Quotient.mk _ (Classical.arbitrary D)⟩

namespace PictureMap
variable (M : PictureMap D)

/-- A literal one-boundary spanning subpairing of a connected genus-zero
map is a tree on the actual rotation vertices. This also rules out retained
loops and duplicate edges: the edge-count bound and connectivity force equality. -/
theorem subpairing_isTree (hG : M.GenusZero) (q : Perm D)
    (hsub : ∀ x, q x = x ∨ q x = M.edge x)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1) :
    (M.subpairingGraph q (M.subpairing_sq q hsub)).IsTree := by
  have hconn := M.subpairing_connected q (M.subpairing_sq q hsub) hspan
  obtain ⟨l,hl,hn,hpairs⟩ := involution_pairs q (M.subpairing_sq q hsub)
  have hedge := M.subpairing_edge_card_le q (M.subpairing_sq q hsub) l hl
    (fun ab hab => (hpairs ab hab).2)
  have heuler := M.subpairing_euler q hsub hG
  rw [hspan,card_quotient_top_one,hboundary,cycles_eq_card_classes] at heuler
  change (Nat.card M.GraphVertex : ℤ) + 1 - (q.support.card : ℤ)/2 = 2 at heuler
  have hnZ : (q.support.card : ℤ) = 2*(l.length : ℤ) := by exact_mod_cast hn.symm
  have hdiv : (q.support.card : ℤ)/2 = (l.length : ℤ) := by
    rw [hnZ]
    omega
  rw [hdiv] at heuler
  have hv : Nat.card M.GraphVertex = l.length+1 := by
    have hh : (Nat.card M.GraphVertex : ℤ) = (l.length : ℤ)+1 := by linarith
    exact_mod_cast hh
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn,?_⟩
  have hlo := hconn.card_vert_le_card_edgeSet_add_one
  omega

/-- Complementary primal and dual TREE graphs, obtained from the real
side-pairing and exact genus-zero equation. No abstract drawing or tree
interface has been substituted for the rotation system. -/
theorem connected_tree_cotree (hG : M.GenusZero) (hconn : M.components = ⊤) :
    ∃ q : Perm D, ∃ hq : ∀ x, q x = x ∨ q x = M.edge x,
      (M.subpairingGraph q (M.subpairing_sq q hq)).IsTree ∧
      (M.dual.subpairingGraph (q*M.edge)
        (M.subpairing_sq (q*M.edge) (M.complement_subpairing q hq))).IsTree := by
  obtain ⟨q,hq,hspan,hb,hdspan,hdb⟩ := M.tree_cotree hG
  have hc : Nat.card (Quotient M.components) = 1 := by
    rw [hconn]; exact card_quotient_top_one
  rw [hc] at hb hdb
  norm_num at hb hdb
  refine ⟨q,hq,M.subpairing_isTree hG q hq (hspan.trans hconn) hb,?_⟩
  apply M.dual.subpairing_isTree (M.dual_genusZero hG) (q*M.edge)
    (M.complement_subpairing q hq)
  · simpa only [M.dual_vertex] using hdspan.trans hconn
  · simpa only [M.dual_vertex] using hdb

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
