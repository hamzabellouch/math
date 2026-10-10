import Mathlib
import OAI.Geometry.HyperbolicGroups.ConnectedLevels

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At most one original connected component can occupy more than half of
a specified carrier. Thus a uniform separator theorem for the actual
connected components extends with the SAME constant to disconnected graphs. -/
theorem component_separators_union (G : SimpleGraph V) (c : ℕ)
    (hcomp : ∀ C : G.ConnectedComponent, ∀ U : Finset C.supp,
      ∃ S : Finset C.supp, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
        ∀ W : Finset C.supp, W ⊆ U → Disjoint W S →
          (C.toSimpleGraph.induce (W : Set C.supp)).Preconnected → 2*W.card ≤ U.card)
    (U : Finset V) :
    ∃ S : Finset V, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
      ∀ W : Finset V, W ⊆ U → Disjoint W S →
        (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card := by
  classical
  have hcolor (W : Finset V) (hc : (G.induce (W : Set V)).Preconnected) :
      ∀ v ∈ W, ∀ w ∈ W, G.connectedComponentMk v = G.connectedComponentMk w :=
    preconnected_color_constant G (W : Set V) hc G.connectedComponentMk
      (fun _ _ _ _ hadj => ConnectedComponent.sound hadj.reachable)
  by_cases hbig : ∃ C : G.ConnectedComponent, U.card < 2*(U.filter (fun v => G.connectedComponentMk v = C)).card
  · obtain ⟨C,hbig⟩ := hbig
    let UC : Finset C.supp := Finset.univ.filter (fun v => v.val ∈ U)
    have hUCimage : UC.image Subtype.val = U.filter (fun v => G.connectedComponentMk v = C) := by
      ext v
      simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,UC]
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨hw,w.property⟩
      · intro hv
        exact ⟨⟨v,hv.2⟩,hv.1,rfl⟩
    have hUCcard : UC.card = (U.filter (fun v => G.connectedComponentMk v = C)).card := by
      rw [← hUCimage,Finset.card_image_of_injective _ Subtype.val_injective]
    have hUCle : UC.card ≤ U.card := hUCcard.trans_le (Finset.card_filter_le _ _)
    obtain ⟨SC,hSCU,hSCcard,hSCsep⟩ := hcomp C UC
    let S := SC.image Subtype.val
    have hSU : S ⊆ U := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp (hSCU hw)).2
    refine ⟨S,hSU,?_,?_⟩
    · rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact hSCcard.trans (Nat.mul_le_mul_left c (Nat.sqrt_le_sqrt hUCle))
    · intro W hWU hWS hc
      by_cases hmeet : ∃ v ∈ W, G.connectedComponentMk v = C
      · obtain ⟨v,hv,hvC⟩ := hmeet
        have hall : ∀ w ∈ W, w ∈ C.supp := by
          intro w hw
          exact (hcolor W hc w hw v hv).trans hvC
        let WC : Finset C.supp := Finset.univ.filter (fun w => w.val ∈ W)
        have hWCimage : WC.image Subtype.val = W := by
          ext w
          simp only [Finset.mem_image,WC,Finset.mem_filter,Finset.mem_univ,true_and]
          constructor
          · rintro ⟨z,hz,rfl⟩; exact hz
          · intro hw; exact ⟨⟨w,hall w hw⟩,hw,rfl⟩
        have hWCcard : WC.card = W.card := by
          rw [← hWCimage,Finset.card_image_of_injective _ Subtype.val_injective]
        have hWCU : WC ⊆ UC := by
          intro w hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hWU (Finset.mem_filter.mp hw).2⟩
        have hWCdisj : Disjoint WC SC := by
          apply Finset.disjoint_left.mpr
          intro w hw hwS
          exact Finset.disjoint_left.mp hWS (Finset.mem_filter.mp hw).2
            (Finset.mem_image.mpr ⟨w,hwS,rfl⟩)
        have hWCconn : (C.toSimpleGraph.induce (WC : Set C.supp)).Preconnected := by
          let g : G.induce (W : Set V) →g C.toSimpleGraph.induce (WC : Set C.supp) := {
            toFun := fun w => ⟨⟨w.val,hall w.val w.property⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _,w.property⟩⟩
            map_rel' := fun h => h }
          apply hc.map g
          intro w
          exact ⟨⟨w.val.val,(Finset.mem_filter.mp w.property).2⟩,Subtype.ext (Subtype.ext rfl)⟩
        have hh := hSCsep WC hWCU hWCdisj hWCconn
        rw [hWCcard] at hh
        exact hh.trans hUCle
      · have hdisj : Disjoint W (U.filter (fun v => G.connectedComponentMk v = C)) := by
          apply Finset.disjoint_left.mpr
          intro v hv hvC
          exact hmeet ⟨v,hv,(Finset.mem_filter.mp hvC).2⟩
        have hsub : W ∪ U.filter (fun v => G.connectedComponentMk v = C) ⊆ U :=
          Finset.union_subset hWU (Finset.filter_subset _ _)
        have hh := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj] at hh
        omega
  · refine ⟨∅,Finset.empty_subset _,by simp,?_⟩
    intro W hWU _ hc
    by_cases he : W.Nonempty
    · obtain ⟨v,hv⟩ := he
      have hsub : W ⊆ U.filter (fun w => G.connectedComponentMk w = G.connectedComponentMk v) := by
        intro w hw
        exact Finset.mem_filter.mpr ⟨hWU hw,hcolor W hc w hw v hv⟩
      have hh := Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)
      have hn := not_lt.mp (fun h => hbig ⟨G.connectedComponentMk v,h⟩)
      exact hh.trans hn
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
