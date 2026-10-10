import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Portion
import OAI.Geometry.Cannon.PlanarGraphs.RegionBoundaryHitsOpen

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

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence CannonPlanarCorner

variable {D : Type*} [TopologicalSpace D] [DiscreteTopology D]

lemma crosscut_incidence_local (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hUa : a '' Ioo (0:I) 1 ⊆ U)
    {π : (U \ range a : Set ℂ) → D} (hπ : Continuous π)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ W : Set ℂ, IsOpen W ∧ a t∈W ∧ ∃ l : Bool → D,
      ∀ x∈W∩range a, incident (U \ range a) π x=range l := by
  obtain ⟨H,W,hW,htW,h₀,hflat⟩ := tame_graph_flat_chart (fun _ : Unit => a)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) Q (fun _ => ha) () ht₀ ht₁
  have htU : a t∈U := hUa ⟨t,⟨ht₀,ht₁⟩,rfl⟩
  have hf : ∀ z∈W∩U, z∈U\range a ↔ (H.symm z).2≠0 := by
    intro z hz
    have he : z∈range a ↔ (H.symm z).2=0 := by
      have hh := hflat z hz.1
      simp only [iUnion_const] at hh
      rw [H.image_eq_preimage_symm] at hh
      exact hh
    simp only [mem_sdiff,hz.2,true_and,he]
  obtain ⟨W',hW',h₀W',_,l,hl⟩ := flat_chart_incidence hπ H (hW.inter hU)
    (h₀.symm ▸ ⟨htW,htU⟩) hf
  refine ⟨W',hW',h₀ ▸ h₀W',l,?_⟩
  intro x hx
  exact hl x ⟨hx.1,fun h => h.2 hx.2⟩

theorem crosscut_incident_labels (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hUa : a '' Ioo (0:I) 1 ⊆ U)
    {π : (U \ range a : Set ℂ) → D} (hπ : Continuous π) :
    ∃ l : Bool → D, ∀ t : I, 0<t → t<1 →
      incident (U\range a) π (a t)=range l := by
  let A := a '' Ioo (0:I) 1
  have hA : IsPreconnected A := isPreconnected_Ioo.image a a.continuous.continuousOn
  have hloc : ∀ x∈A, ∃ W : Set ℂ, IsOpen W ∧ x∈W ∧
      ∀ y∈A∩W, incident (U\range a) π y=incident (U\range a) π x := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨W,hW,htW,l,hl⟩ := crosscut_incidence_local a Q ha hU hUa hπ ht.1 ht.2
    refine ⟨W,hW,htW,?_⟩
    rintro y ⟨⟨s,hs,hsy⟩,hyW⟩
    exact (hl y ⟨hyW,⟨s,hsy⟩⟩).trans (hl (a t) ⟨htW,mem_range_self t⟩).symm
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm₀ : 0 < m := by change (0:ℝ)<1/2; norm_num
  have hm₁ : m<1 := by change (1/2:ℝ)<1; norm_num
  obtain ⟨W,hW,hmW,l,hl⟩ := crosscut_incidence_local a Q ha hU hUa hπ hm₀ hm₁
  refine ⟨l,fun t ht₀ ht₁ => ?_⟩
  exact (incident_constant_on_preconnected hA hloc (a t) ⟨t,⟨ht₀,ht₁⟩,rfl⟩
    (a m) ⟨m,⟨hm₀,hm₁⟩,rfl⟩).trans (hl (a m) ⟨hmW,mem_range_self m⟩)

theorem crosscut_labels_surjective (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hUa : a '' Ioo (0:I) 1 ⊆ U) (ha₀ : a 0∉U) (ha₁ : a 1∉U)
    {π : (U \ range a : Set ℂ) → D} (hπ : Continuous π) (hπs : Function.Surjective π) :
    ∃ l : Bool → D, Function.Surjective l ∧ ∀ t : I, 0<t → t<1 →
      incident (U\range a) π (a t)=range l := by
  have hV : IsOpen (U\range a) := hU.sdiff a.compact_range.isClosed
  obtain ⟨l,hl⟩ := crosscut_incident_labels a Q ha hU hUa hπ
  refine ⟨l,?_,hl⟩
  intro d
  have hne : (U\(U\range a)).Nonempty := by
    let m : I := ⟨1/2,by constructor <;> norm_num⟩
    have hm : 0 < m ∧ m<1 := by change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1; constructor <;> norm_num
    exact ⟨a m,hUa ⟨m,hm,rfl⟩,fun h => h.2 (mem_range_self m)⟩
  obtain ⟨z,⟨hzU',hzV⟩,hzd⟩ := region_boundary_hits_in_open hU hV sdiff_subset hconn hne hπ d
    (by obtain ⟨z,hz⟩ := hπs d; exact ⟨z,z.property,hz⟩)
  have hza : z∈range a := by by_contra h; exact hzV ⟨hzU',h⟩
  obtain ⟨t,rfl⟩ := hza
  have ht₀ : 0<t := lt_of_le_of_ne (unitInterval.nonneg t) (fun h => ha₀ (h ▸ hzU'))
  have ht₁ : t<1 := lt_of_le_of_ne (unitInterval.le_one t) (fun h => ha₁ (h ▸ hzU'))
  rw [hl t ht₀ ht₁] at hzd
  exact hzd
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem crosscut_not_preconnected (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hUa : a '' Ioo (0:I) 1 ⊆ U) (hbU : range b⊆Uᶜ) :
    ¬IsPreconnected (U\range a) := by
  let K := range a∪range b
  have hK : IsClosed K := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  obtain ⟨l,hl⟩ := tame_pair_jordan a b hab₀ hab₁ hc Q ha hb
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm : 0 < m ∧ m<1 := by change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1; constructor <;> norm_num
  have hmU : a m∈U := hUa ⟨m,hm,rfl⟩
  have hVsub : U\range a ⊆ Kᶜ := by
    rintro z ⟨hzU,hza⟩ (hza'|hzb)
    · exact hza hza'
    · exact hbU hzb hzU
  have hmeet (i : Bool) : (U∩region Kᶜ ConnectedComponents.mk (l i)).Nonempty := by
    have hmi : a m∈closure (region Kᶜ ConnectedComponents.mk (l i)) := by
      show l i∈incident _ ConnectedComponents.mk (a m)
      rw [hl (a m) (Or.inl (mem_range_self m))]
      exact mem_range_self i
    exact (mem_closure_iff_nhds.mp hmi) U (hU.mem_nhds hmU)
  obtain ⟨x,hxU,hxK,hxl⟩ := hmeet false
  obtain ⟨y,hyU,hyK,hyl⟩ := hmeet true
  have hxV : x∈U\range a := ⟨hxU,fun h => hxK (Or.inl h)⟩
  have hyV : y∈U\range a := ⟨hyU,fun h => hyK (Or.inl h)⟩
  intro hconn
  obtain ⟨d,hd⟩ := label_on_connected ConnectedComponents.continuous_coe
    ⟨⟨x,hxV⟩,hconn⟩ hVsub
  have he : l false=l true := hxl.symm.trans ((hd hxV).2.trans ((hd hyV).2.symm.trans hyl))
  exact Bool.false_ne_true (l.injective he)

theorem tame_crosscut_components (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hUa : a '' Ioo (0:I) 1 ⊆ U) (hbU : range b⊆Uᶜ) :
    ∃ l : Bool ≃ ConnectedComponents (U\range a : Set ℂ),
      ∀ t : I, 0<t → t<1 → incident (U\range a) ConnectedComponents.mk (a t)=range l := by
  have hV : IsOpen (U\range a) := hU.sdiff a.compact_range.isClosed
  let _ : LocallyConnectedSpace (U\range a : Set ℂ) := hV.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (U\range a : Set ℂ)) := inferInstance
  have ha₀ : a 0∉U := hab₀ ▸ hbU (mem_range_self 0)
  have ha₁ : a 1∉U := hab₁ ▸ hbU (mem_range_self 1)
  obtain ⟨l,hls,hl⟩ := crosscut_labels_surjective a Q ha hU hconn hUa ha₀ ha₁
    ConnectedComponents.continuous_coe ConnectedComponents.surjective_coe
  have hne : l false≠l true := by
    intro he
    have hconst (s t : Bool) : l s=l t := by
      cases s <;> cases t
      · rfl
      · exact he
      · exact he.symm
      · rfl
    have hsub (d e : ConnectedComponents (U\range a : Set ℂ)) : d=e := by
      obtain ⟨s,rfl⟩ := hls d
      obtain ⟨t,rfl⟩ := hls e
      exact hconst s t
    have hcon : PreconnectedSpace (U\range a : Set ℂ) := by
      rw [preconnectedSpace_iff_connectedComponent]
      intro x
      apply eq_univ_of_forall
      intro y
      exact ConnectedComponents.coe_eq_coe'.mp (hsub _ _)
    exact crosscut_not_preconnected a b hab₀ hab₁ hc Q ha hb hU hUa hbU
      (isPreconnected_iff_preconnectedSpace.mpr hcon)
  have hli : Function.Injective l := by
    intro s t h
    cases s <;> cases t
    · rfl
    · exact (hne h).elim
    · exact (hne h.symm).elim
    · rfl
  exact ⟨Equiv.ofBijective l ⟨hli,hls⟩,hl⟩
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

end OAI
