import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.HalfParam
import OAI.Geometry.Cannon.PlanarGraphs.FlatChartBoundaryPatch

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
open Set Topology Metric unitInterval CannonFaceIncidence

theorem noncut_cycle_free_region {K : Set ℂ}
    (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hb : range b⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hK : IsConnected (K\{a 1}))
    (hCK : (range a∪range b)\{a 1}⊆Kᶜ) :
    ∃ d : ConnectedComponents ((range a∪range b)ᶜ : Set ℂ),
      (∀ z∈range a∪range b,d∈incident _ ConnectedComponents.mk z) ∧
      closure (region _ ConnectedComponents.mk d)\{a 1}⊆connectedComponentIn Kᶜ (a 0) := by
  let C : Set ℂ := range a∪range b
  have hC : IsClosed C := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Cᶜ : Set ℂ) := hC.isOpen_compl.locallyConnectedSpace
  have hqC : a 1∈C := Or.inl (mem_range_self 1)
  obtain ⟨l,hl⟩ := tame_pair_jordan a b hab₀ hab₁ hc Q ha hb
  have hKC : K\{a 1}⊆Cᶜ := by
    intro z hz hzC
    exact hCK ⟨hzC,hz.2⟩ hz.1
  obtain ⟨d,hd⟩ := label_on_connected ConnectedComponents.continuous_coe hK hKC
  let i := l.symm d
  let e := l (!i)
  let R := region Cᶜ ConnectedComponents.mk e
  have hRconn : IsConnected R := component_region_connected _ _
  have hRi : R⊆Kᶜ := by
    intro z hz hzK
    have hzq : z≠a 1 := fun h => (region_subset _ _ _ hz) (h.symm ▸ hqC)
    obtain ⟨_,he⟩ := hd ⟨hzK,hzq⟩
    obtain ⟨_,he'⟩ := hz
    have hh : (!i)=i := l.injective (he'.symm.trans (he.trans (l.apply_symm_apply d).symm))
    cases i <;> simp at hh
  have hRcl : closure R=R∪C := by
    apply Subset.antisymm
    · intro z hz
      by_cases hzC : z∈C
      · exact Or.inr hzC
      · exact Or.inl (closure_region_inside hC.isOpen_compl ConnectedComponents.continuous_coe hz hzC)
    · apply union_subset subset_closure
      intro z hz
      change e∈incident _ ConnectedComponents.mk z
      rw [hl z hz]
      exact mem_range_self (!i)
  have hRnoq : R⊆closure R\{a 1} := by
    intro z hz
    exact ⟨subset_closure hz,fun he => (region_subset _ _ _ hz) (he.symm ▸ hqC)⟩
  have hpre : IsPreconnected (closure R\{a 1}) :=
    hRconn.isPreconnected.subset_closure hRnoq sdiff_subset
  have hsub : closure R\{a 1}⊆Kᶜ := by
    rintro z ⟨hz,hzq⟩
    rw [hRcl] at hz
    exact hz.elim (fun h => hRi h) (fun h => hCK ⟨h,hzq⟩)
  have hxcl : a 0∈closure R\{a 1} := by
    rw [hRcl]
    exact ⟨Or.inr (Or.inl (mem_range_self 0)),a.endpoints_ne⟩
  refine ⟨e,?_,hpre.subset_connectedComponentIn hxcl hsub⟩
  intro z hz
  rw [hl z hz]
  exact mem_range_self (!i)
end CannonEmbeddedArc.Arc

namespace CannonSegmentCones
open Set Metric Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma local_component_radial {K : Set E} {q : E} {r : ℝ}
    (hstable : RadialStable K q r) {a z : E}
    (hz : z∈connectedComponentIn (ball q r\K) a) {t : ℝ} (ht : 0<t) (ht₁ : t≤1) :
    q+t • (z-q)∈connectedComponentIn (ball q r\K) a := by
  let S : Set E := (fun u : ℝ => q+u • (z-q)) '' Ioc 0 1
  have hzV := connectedComponentIn_subset (ball q r\K) a hz
  have hS : IsPreconnected S := isPreconnected_Ioc.image _ (by fun_prop)
  have hSV : S⊆ball q r\K := by
    rintro w ⟨u,hu,rfl⟩
    exact ⟨radial_mem_ball hzV.1 hu.1.le hu.2,fun h => hzV.2 ((hstable z hzV.1 u hu.1 hu.2).mp h)⟩
  have hzS : z∈S := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
  have hSC := hS.subset_connectedComponentIn hzS hSV
  have he := connectedComponentIn_eq hz
  rw [←he] at hSC
  exact hSC ⟨t,⟨ht,ht₁⟩,rfl⟩
end CannonSegmentCones

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPolygonal CannonFaceIncidence CannonSegmentCones

theorem noncut_radial_germs_join (P : Finset (ℂ × ℂ)) {q a x : ℂ}
    (hqK : q∈⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsConnected ((⋃ p∈P,segment ℝ p.1 p.2)\{q}))
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (C : Fin 2 → Set ℂ) (hC : ∀ i,IsOpen (C i)) (hqC : ∀ i,q∈closure (C i))
    (hCU : ∀ i,C i⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ i,∀ z∈C i,∀ t : ℝ,0<t → t≤1 → q+t • (z-q)∈C i)
    {r : ℝ} (hr : 0<r) :
    ∃ B : Set ℂ,IsConnected B ∧
      B⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a∩ball q r ∧
      ∀ i,(B∩C i).Nonempty := by
  classical
  let K : Set ℂ := ⋃ p∈P,segment ℝ p.1 p.2
  let U := connectedComponentIn Kᶜ a
  obtain ⟨F,hF,h₀,h₁,hS,hFU,hgerm⟩ := finite_prescribed_star P hx 2 (fun _ => q) C
    (fun _ => hqK) hC hqC hCU hrad
  let b := F 0
  let c := F 1
  have hbc₀ : b 0=c 0 := (h₀ 0).trans (h₀ 1).symm
  have hbc₁ : b 1=c 1 := (h₁ 0).trans (h₁ 1).symm
  have hbc : ∀ s t,b s=c t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := hF (by decide : (0:Fin 2)≠1)
  obtain ⟨Q,hQ⟩ := (hS 0).union (hS 1)
  have hbQ : range b⊆⋃ p∈Q,segment ℝ p.1 p.2 := fun z hz => hQ (Or.inl hz)
  have hcQ : range c⊆⋃ p∈Q,segment ℝ p.1 p.2 := fun z hz => hQ (Or.inr hz)
  have hFnot (i : Fin 2) {t : I} (ht : t≠1) : F i t∈U := by
    by_cases ht₀ : t=0
    · simpa only [ht₀,h₀] using hx
    · exact hFU i ⟨t,⟨lt_of_le_of_ne (nonneg t) (Ne.symm ht₀),
        lt_of_le_of_ne (le_one t) ht⟩,rfl⟩
  have hCK : (range b∪range c)\{b 1}⊆Kᶜ := by
    rintro z ⟨hz,hzq⟩
    rcases hz with ⟨t,rfl⟩|⟨t,rfl⟩
    · exact connectedComponentIn_subset Kᶜ a (hFnot 0 (fun he => hzq (congrArg b he)))
    · exact connectedComponentIn_subset Kᶜ a (hFnot 1 (fun he => hzq ((congrArg c he).trans hbc₁.symm)))
  have hconn : IsConnected (K\{b 1}) := by simpa only [b,h₁] using hK
  obtain ⟨d,hd,hfree⟩ := noncut_cycle_free_region b c hbc₀ hbc₁ hbc Q hbQ hcQ hconn hCK
  have hBU : closure (region _ ConnectedComponents.mk d)\{q}⊆U := by
    have he : connectedComponentIn Kᶜ (b 0)=U := by
      rw [show b 0=x from h₀ 0]
      exact (connectedComponentIn_eq hx).symm
    simpa only [show b 1=q from h₁ 0,he] using hfree
  let L : Set ℂ := range b∪range c
  have hL : IsClosed L := b.compact_range.isClosed.union c.compact_range.isClosed
  let _ : LocallyConnectedSpace (Lᶜ : Set ℂ) := hL.isOpen_compl.locallyConnectedSpace
  obtain ⟨H,W,hW,hqW,hH,hflat⟩ := pair_flat_at_left b c hbc₀ hbc₁ hbc Q hbQ hcQ 1
  have hHq : H (0,0)=q := hH.trans (h₁ 0)
  have hqW' : q∈W∩ball q r := ⟨(h₁ 0) ▸ hqW,mem_ball_self hr⟩
  have hflat' : ∀ z∈W∩ball q r,z∈Lᶜ ↔ (H.symm z).2≠0 := by
    intro z hz
    rw [mem_compl_iff,hflat z hz.1]
    have hh : z∈H '' CannonPlanarCorner.horizontal ↔ (H.symm z).2=0 := by
      constructor
      · rintro ⟨y,hy,rfl⟩
        simpa only [H.symm_apply_apply,CannonPlanarCorner.horizontal,mem_ofPred_eq] using hy
      · intro hy
        exact ⟨H.symm z,hy,H.apply_symm_apply z⟩
    rw [hh]
  obtain ⟨V,B,hV,hqV,hVW,hB,hBW,hBcl⟩ := flat_chart_boundary_patch
    ConnectedComponents.continuous_coe H (hW.inter isOpen_ball) (hHq.symm ▸ hqW') hflat'
    (d:=d) (by rw [hHq]; exact hd q (Or.inl ⟨1,h₁ 0⟩))
  have hqV' : q∈V := hHq ▸ hqV
  have hBV : B⊆U∩ball q r := by
    intro z hz
    have hh := hBW hz
    refine ⟨hBU ⟨subset_closure hh.2,?_⟩,hh.1.2⟩
    intro he
    exact (region_subset _ _ _ hh.2) (he.symm ▸ Or.inl ⟨1,h₁ 0⟩)
  refine ⟨B,hB,hBV,?_⟩
  intro i
  obtain ⟨ε,hε,hεg⟩ := hgerm i
  let N := V∩ball q ε
  have hN : IsOpen N := hV.inter isOpen_ball
  have hqN : q∈N := ⟨hqV',mem_ball_self hε⟩
  obtain ⟨t,ht,htN⟩ := (dense_compl_singleton (1:I)).exists_mem_open
    ((F i).continuous.isOpen_preimage N hN) ⟨1,by change F i 1∈N; rw [h₁]; exact hqN⟩
  have htq : F i t≠q := fun he => ht ((F i).injective (he.trans (h₁ i).symm))
  have htC : F i t∈C i := (hεg ⟨mem_range_self t,htN.2⟩).resolve_left htq
  have htL : F i t∈L := by
    fin_cases i
    · exact Or.inl (mem_range_self t)
    · exact Or.inr (mem_range_self t)
  have htcl : F i t∈closure B := hBcl ⟨htN.1,by simpa only [compl_compl] using htL⟩
  obtain ⟨z,hzC,hzB⟩ := (mem_closure_iff_nhds.mp htcl) (C i) ((hC i).mem_nhds htC)
  exact ⟨z,hzB,hzC⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPolygonal CannonFaceIncidence CannonSegmentCones

theorem noncut_face_ball_preconnected (P : Finset (ℂ × ℂ)) {q : ℂ}
    (hqK : q∈⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsConnected ((⋃ p∈P,segment ℝ p.1 p.2)\{q}))
    {r : ℝ} (hr : 0<r) (hstable : RadialStable (⋃ p∈P,segment ℝ p.1 p.2) q r) :
    ∀ a : ℂ,IsPreconnected
      (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a∩ball q r) := by
  classical
  let K : Set ℂ := ⋃ p∈P,segment ℝ p.1 p.2
  have hKclosed : IsClosed K := isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  let V := ball q r\K
  have hV : IsOpen V := isOpen_ball.sdiff hKclosed
  intro a
  let U := connectedComponentIn Kᶜ a
  by_cases hne : (U∩ball q r).Nonempty
  · obtain ⟨x,hxU,hxr⟩ := hne
    have hxV : x∈V := ⟨hxr,connectedComponentIn_subset Kᶜ a hxU⟩
    have hsub {z : ℂ} (hz : z∈U∩ball q r) : connectedComponentIn V z⊆U∩ball q r := by
      have hzV : z∈V := ⟨hz.2,connectedComponentIn_subset Kᶜ a hz.1⟩
      have h := (isPreconnected_connectedComponentIn (F:=V) (x:=z)).subset_connectedComponentIn
        (mem_connectedComponentIn hzV) (fun w hw => (connectedComponentIn_subset V z hw).2)
      have he : U=connectedComponentIn Kᶜ z := connectedComponentIn_eq hz.1
      change connectedComponentIn V z⊆connectedComponentIn Kᶜ z at h
      rw [←he] at h
      exact fun w hw => ⟨h hw,(connectedComponentIn_subset V z hw).1⟩
    have heq : U∩ball q r=connectedComponentIn V x := by
      apply Subset.antisymm ?_ (hsub ⟨hxU,hxr⟩)
      intro y hy
      let Z : Fin 2 → ℂ := ![x,y]
      have hZ : ∀ i,Z i∈U∩ball q r := by
        intro i
        fin_cases i
        · exact ⟨hxU,hxr⟩
        · exact hy
      let C : Fin 2 → Set ℂ := fun i => connectedComponentIn V (Z i)
      have hZV (i : Fin 2) : Z i∈V := ⟨(hZ i).2,connectedComponentIn_subset Kᶜ a (hZ i).1⟩
      have hCopen (i : Fin 2) : IsOpen (C i) := hV.connectedComponentIn
      have hCrad (i : Fin 2) : ∀ z∈C i,∀ t : ℝ,0<t → t≤1 → q+t • (z-q)∈C i :=
        fun _ hz _ ht ht₁ => local_component_radial hstable hz ht ht₁
      have hCcl (i : Fin 2) : q∈closure (C i) := CannonSectors.radial_vertex_closure
        ⟨Z i,mem_connectedComponentIn (hZV i)⟩ (hCrad i)
      have hCU (i : Fin 2) : C i⊆U := (hsub (hZ i)).trans inter_subset_left
      obtain ⟨B,hB,hBV,hBC⟩ := noncut_radial_germs_join P hqK hK hxU C hCopen hCcl hCU hCrad hr
      obtain ⟨z,hzB,hzC⟩ := hBC 0
      have hBV' : B⊆V := fun w hw => ⟨(hBV hw).2,connectedComponentIn_subset Kᶜ a (hBV hw).1⟩
      have hBC₀ := hB.isPreconnected.subset_connectedComponentIn hzB hBV'
      have he₀ : C 0=connectedComponentIn V z := connectedComponentIn_eq hzC
      rw [←he₀] at hBC₀
      obtain ⟨w,hwB,hwC⟩ := hBC 1
      have he₁ : C 1=connectedComponentIn V w := connectedComponentIn_eq hwC
      have he₂ : C 0=connectedComponentIn V w := connectedComponentIn_eq (hBC₀ hwB)
      have hyC : y∈C 1 := mem_connectedComponentIn (hZV 1)
      rw [he₁,←he₂] at hyC
      exact hyC
    rw [heq]
    exact isPreconnected_connectedComponentIn
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty
theorem noncut_locally_connected_faces (P : Finset (ℂ × ℂ)) {q : ℂ}
    (hqK : q∈⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsConnected ((⋃ p∈P,segment ℝ p.1 p.2)\{q})) :
    ∃ r>0,∀ s : ℝ,0<s → s≤r → ∀ a : ℂ,IsPreconnected
      (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a∩ball q s) := by
  obtain ⟨r,hr,hstable⟩ := finite_segments_radial_stable P q
  exact ⟨r,hr,fun _ hs hsr => noncut_face_ball_preconnected P hqK hK hs (hstable.mono_radius hsr)⟩
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
