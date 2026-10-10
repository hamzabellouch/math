import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.ComponentRegion
import OAI.Geometry.Cannon.PlaneTopology.RadialStable
import OAI.Geometry.Cannon.PlanarGraphs.HomeomorphComponents

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal

lemma other_component_delete_arc (K : Set ℂ) (a : Arc ℂ) (d : ConnectedComponents (Kᶜ : Set ℂ))
    (h₀ : a 0∈K ∨ a 0∈region Kᶜ ConnectedComponents.mk d)
    (h₁ : a 1∈K ∨ a 1∈region Kᶜ ConnectedComponents.mk d)
    (hU : a '' Ioo (0:I) 1⊆region Kᶜ ConnectedComponents.mk d)
    (e : ConnectedComponents (Kᶜ : Set ℂ)) (hed : e≠d) :
    region Kᶜ ConnectedComponents.mk e\range a=region Kᶜ ConnectedComponents.mk e := by
  apply sdiff_eq_left.mpr
  apply Set.disjoint_left.mpr
  rintro x hx ⟨t,rfl⟩
  have hn : a t∉region Kᶜ ConnectedComponents.mk d :=
    Set.disjoint_left.mp (region_disjoint_components Kᶜ hed) hx
  by_cases ht₀ : t=0
  · subst t
    exact h₀.elim hx.1 hn
  by_cases ht₁ : t=1
  · subst t
    exact h₁.elim hx.1 hn
  exact hn (hU ⟨t,⟨lt_of_le_of_ne (nonneg t) (Ne.symm ht₀),lt_of_le_of_ne (le_one t) ht₁⟩,rfl⟩)

theorem leaf_face_count (K : Set ℂ) (hK : IsClosed K)
    [Finite (ConnectedComponents (Kᶜ : Set ℂ))]
    (a : Arc ℂ) (Q : Finset (ℂ × ℂ)) (ha : range a⊆⋃q∈Q,segment ℝ q.1 q.2)
    (d : ConnectedComponents (Kᶜ : Set ℂ))
    (h₀ : a 0∈region Kᶜ ConnectedComponents.mk d) (h₁ : a 1∈K)
    (hU : a '' Ioo (0:I) 1⊆region Kᶜ ConnectedComponents.mk d) :
    Nat.card (ConnectedComponents ((K∪range a)ᶜ : Set ℂ))=
      Nat.card (ConnectedComponents (Kᶜ : Set ℂ)) := by
  classical
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  let _ := Fintype.ofFinite (ConnectedComponents (Kᶜ : Set ℂ))
  have hconn (e : ConnectedComponents (Kᶜ : Set ℂ)) :
      IsConnected (region Kᶜ ConnectedComponents.mk e\range a) := by
    by_cases hed : e=d
    · subst e
      exact tame_slit_connected a Q ha
        (region_isOpen hK.isOpen_compl ConnectedComponents.continuous_coe d)
        (component_region_connected Kᶜ d).isPreconnected h₀ hU (fun h => h.1 h₁)
    · rw [other_component_delete_arc K a d (Or.inr h₀) (Or.inl h₁) hU e hed]
      exact component_region_connected Kᶜ e
  let _ (e : ConnectedComponents (Kᶜ : Set ℂ)) : ConnectedSpace
      (region Kᶜ ConnectedComponents.mk e\range a : Set ℂ) := isConnected_iff_connectedSpace.mp (hconn e)
  have heq : (K∪range a)ᶜ=Kᶜ\range a := by ext z; simp
  rw [heq,Nat.card_congr (componentsDeletionEquiv Kᶜ (range a)),Nat.card_sigma]
  simp only [connected_components_card_one (hconn _),Finset.sum_const,Finset.card_univ,
    smul_eq_mul,mul_one,Nat.card_eq_fintype_card]

theorem crosscut_face_count (P Q : Finset (ℂ × ℂ))
    (hK : IsPreconnected (⋃p∈P,segment ℝ p.1 p.2))
    [Finite (ConnectedComponents ((⋃p∈P,segment ℝ p.1 p.2)ᶜ : Set ℂ))]
    (a : Arc ℂ) (ha : range a⊆⋃q∈Q,segment ℝ q.1 q.2)
    (d : ConnectedComponents ((⋃p∈P,segment ℝ p.1 p.2)ᶜ : Set ℂ))
    (h₀ : a 0∈⋃p∈P,segment ℝ p.1 p.2) (h₁ : a 1∈⋃p∈P,segment ℝ p.1 p.2)
    (hU : a '' Ioo (0:I) 1⊆region _ ConnectedComponents.mk d) :
    Nat.card (ConnectedComponents (((⋃p∈P,segment ℝ p.1 p.2)∪range a)ᶜ : Set ℂ))=
      Nat.card (ConnectedComponents ((⋃p∈P,segment ℝ p.1 p.2)ᶜ : Set ℂ))+1 := by
  classical
  let K : Set ℂ := ⋃p∈P,segment ℝ p.1 p.2
  have hKc : IsClosed K := isClosed_biUnion_finset fun p _ => CannonSegmentCones.segment_closed p.1 p.2
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hKc.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  let _ := Fintype.ofFinite (ConnectedComponents (Kᶜ : Set ℂ))
  obtain ⟨l,hl⟩ := connected_graph_crosscut P Q hK a ha h₀ h₁
    (region_isOpen hKc.isOpen_compl ConnectedComponents.continuous_coe d)
    (component_region_connected Kᶜ d).isPreconnected (region_subset _ _ d) hU
  let _ : Finite (ConnectedComponents (region Kᶜ ConnectedComponents.mk d\range a : Set ℂ)) :=
    Finite.of_equiv Bool l
  have hcd : Nat.card (ConnectedComponents (region Kᶜ ConnectedComponents.mk d\range a : Set ℂ))=2 :=
    (Nat.card_congr l.symm).trans (by simp)
  have hother (e : ConnectedComponents (Kᶜ : Set ℂ)) (hed : e≠d) :
      IsConnected (region Kᶜ ConnectedComponents.mk e\range a) := by
    rw [other_component_delete_arc K a d (Or.inl h₀) (Or.inl h₁) hU e hed]
    exact component_region_connected Kᶜ e
  let _ (e : ConnectedComponents (Kᶜ : Set ℂ)) :
      Finite (ConnectedComponents (region Kᶜ ConnectedComponents.mk e\range a : Set ℂ)) := by
    by_cases he : e=d
    · subst e; infer_instance
    · let _ : ConnectedSpace (region Kᶜ ConnectedComponents.mk e\range a : Set ℂ) :=
        isConnected_iff_connectedSpace.mp (hother e he)
      infer_instance
  have heq : (K∪range a)ᶜ=Kᶜ\range a := by ext z; simp
  change Nat.card (ConnectedComponents ((K∪range a)ᶜ : Set ℂ))=Nat.card (ConnectedComponents (Kᶜ : Set ℂ))+1
  rw [heq,Nat.card_congr (componentsDeletionEquiv Kᶜ (range a)),Nat.card_sigma]
  have hcount (e : ConnectedComponents (Kᶜ : Set ℂ)) :
      Nat.card (ConnectedComponents (region Kᶜ ConnectedComponents.mk e\range a : Set ℂ))=1+if e=d then 1 else 0 := by
    by_cases he : e=d
    · subst e; simp [hcd]
    · simp [he,connected_components_card_one (hother e he)]
  simp_rw [hcount]
  simp [Finset.sum_add_distrib,Nat.card_eq_fintype_card]
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
