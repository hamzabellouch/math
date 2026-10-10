import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.SquareSide
import OAI.Geometry.Cannon.PlanarGraphs.NetJoined

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

namespace CannonEmbeddedArc.Arc
variable {X : Type*} [TopologicalSpace X]
lemma intersectionCount_embedding {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Arc X) (e : κ ↪ ι) (S : Set X) :
    intersectionCount (E ∘ e) S ≤ intersectionCount E S := by
  classical
  simp only [intersectionCount_eq_card]
  apply Finset.card_le_card_of_injOn e
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact e.injective h

end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
variable {X : Type*} [MetricSpace X]

theorem connected_core [PreconnectedSpace X] [Nonempty X]
    {r : ℝ} (hr : 0<r) {n : ℕ} (F : Fin n → Arc X) (T : Set X)
    (hcover : ∀ x : X, ∃ t∈T, dist x t≤r)
    (hjoin : ∀ x∈T, ∀ y∈T, dist x y<4*r → JoinedIn ((⋃ i, range (F i))∪T) x y) :
    ∃ m : ℕ, ∃ e : Fin m ↪ Fin n,
      IsPathConnected ((⋃ j, range (F (e j)))∪T) ∧
      (∀ x∈T, ∀ y : X, ∀ p : Path x y,
        range p⊆(⋃ i, range (F i)) → range p⊆(⋃ j, range (F (e j)))) := by
  classical
  obtain ⟨a,ha,_⟩ := hcover (Classical.choice (inferInstance : Nonempty X))
  let Q := (⋃ i, range (F i))∪T
  have haQ : a∈Q := Or.inr ha
  have hT := CannonGraphCore.net_joined hr T Q subset_union_right hcover hjoin ha
  let J := {i : Fin n // F i 0∈pathComponentIn Q a}
  let eqv := (Fintype.equivFin J).symm
  let e : Fin (Fintype.card J) ↪ Fin n := ⟨fun j => (eqv j).val,
    Subtype.val_injective.comp eqv.injective⟩
  have hs : (⋃ j, range (F (e j)))=⋃ j : J, range (F j.val) := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨eqv j,hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨eqv.symm j,by simpa only [e,Function.Embedding.coeFn_mk,eqv.apply_symm_apply] using hj⟩
  have hcore : pathComponentIn Q a=(⋃ j, range (F (e j)))∪T := by
    rw [hs]
    exact CannonGraphCore.component_whole_edges (fun i => (F i).map) T a ha hT
  refine ⟨Fintype.card J,e,?_,?_⟩
  · rw [←hcore]
    exact isPathConnected_pathComponentIn haQ
  · intro x hx y p hp z hz
    have hzP := CannonGraphCore.path_range_in_component (hT x hx) p (hp.trans subset_union_left) hz
    rw [hs]
    exact CannonGraphCore.component_retains_edges (fun i => (F i).map) subset_union_left hzP (hp hz)
end CannonEmbeddedArc.Arc

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_connected_loop_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A B r₀ : ℝ, 1≤A ∧ 0<B ∧ 0<r₀ ∧ ∃ K : ℕ,
      ∀ r : ℝ, 0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y≤r) →
      ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        IsPathConnected ((⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
        (∀ (f : C(I,Boundary D)), f 0=f 1 →
          ∃ H : C(I×I,Boundary D), (∀ t, H (0,t)=f t) ∧
            (∀ t, H (1,t)∈(⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
            (∀ s, H (s,0)=H (s,1)) ∧
            (∀ s s' t, dist (H (s,t)) (H (s',t))<B*r)) := by
  let _ := visualMetricSpace D hδ
  let _ : PathConnectedSpace SphereTwo := CannonPaths.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  dsimp only
  obtain ⟨A,rG,hA,hrG,K,hgraph⟩ := boundary_uniform_embedded_graph D hδ φ
  obtain ⟨L,rA,hL,hrA,harc⟩ := boundary_controlled_embedded_arcs D hδ φ
  obtain ⟨c,hc,_,hdisks⟩ := boundary_controlled_regular_disks D hδ φ
  let M := max A L
  have hM : 1≤M := hA.trans (le_max_left ..)
  have hMp : 0<3*M+2 := by linarith
  let C := (3*M+2)/c
  have hC : 0<C := div_pos hMp hc
  refine ⟨A,2*C,min rG (min rA (c/(3*M+2))),hA,by positivity,
    lt_min hrG (lt_min hrA (div_pos hc hMp)),K,?_⟩
  intro r hr hrs T hsep hcover
  obtain ⟨n₀,F₀,hFc₀,hFj₀,hFd₀,hFt₀⟩ := hgraph r hr (hrs.trans (min_le_left ..)) T hsep
  have hjoin₀ (x : Boundary D) (hx : x∈(T:Set (Boundary D)))
      (y : Boundary D) (hy : y∈(T:Set (Boundary D))) (hd : dist x y<4*r) :
      JoinedIn ((⋃ j, range (F₀ j))∪(T:Set (Boundary D))) x y := by
    by_cases heq : x=y
    · subst y
      exact JoinedIn.refl (Or.inr hx)
    · obtain ⟨_,_,b,hb₀,hb₁,hbs,_⟩ := hFj₀ x hx y hy heq hd
      exact ⟨⟨b.map,hb₀,hb₁⟩,fun t => Or.inl (hbs (mem_range_self t))⟩
  obtain ⟨n,e,hconn,hretain⟩ := connected_core hr F₀ (T:Set (Boundary D)) hcover hjoin₀
  let F := F₀ ∘ e
  have hFc : Pairwise (fun i j => Compatible (F i) (F j)) := fun i j hij =>
    hFc₀ (fun h => hij (e.injective h))
  have hFd (j : Fin n) : diam (range (F j))≤A*r := hFd₀ (e j)
  have hFt (x : Boundary D) : intersectionCount F (ball x (2*A*r))≤K :=
    (intersectionCount_embedding F₀ e _).trans (hFt₀ x)
  have hFj (x : Boundary D) (hx : x∈T) (y : Boundary D) (hy : y∈T)
      (hne : x≠y) (hd : dist x y<4*r) :
      ∃ b : Arc (Boundary D), b 0=x ∧ b 1=y ∧
        range b⊆(⋃ j, range (F j)) ∧ diam (range b)≤3*A*r := by
    obtain ⟨_,_,b,hb₀,hb₁,hbs,hbd⟩ := hFj₀ x hx y hy hne hd
    exact ⟨b,hb₀,hb₁,hretain x hx y ⟨b.map,hb₀,hb₁⟩ hbs,hbd⟩
  refine ⟨n,F,hFc,hFd,hFt,hconn,?_⟩
  intro f hf
  have hcon (x y : Boundary D) (hd : dist x y≤r) :
      ∃ p : Path x y, ∀ t, dist (p t) x≤M*r := by
    by_cases heq : x=y
    · subst y
      exact ⟨Path.refl x,fun t => by simp; positivity⟩
    · obtain ⟨a,ha₀,ha₁,hs,_⟩ := harc r hr
        (hrs.trans ((min_le_right ..).trans (min_le_left ..))) x y heq (by linarith)
      refine ⟨⟨a.map,ha₀,ha₁⟩,fun t => ?_⟩
      have h := hs (mem_range_self t)
      change dist (a t) x<L*r at h
      exact h.le.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hr.le)
  have hj (x : Boundary D) (hx : x∈(T:Set (Boundary D)))
      (y : Boundary D) (hy : y∈(T:Set (Boundary D))) (hd : dist x y<4*r) :
      ∃ p : Path x y, range p⊆(⋃ j, range (F j))∪(T:Set (Boundary D)) ∧
        ∀ t, dist (p t) x≤3*M*r := by
    by_cases heq : x=y
    · subst y
      refine ⟨Path.refl x,?_,fun t => by simp; positivity⟩
      rintro z ⟨t,rfl⟩
      exact Or.inr hx
    · obtain ⟨b,hb₀,hb₁,hbs,hbd⟩ := hFj x hx y hy heq hd
      refine ⟨⟨b.map,hb₀,hb₁⟩,hbs.trans subset_union_left,fun t => ?_⟩
      have h := dist_le_diam_of_mem b.compact_range.isBounded (mem_range_self t) (mem_range_self 0)
      rw [hb₀] at h
      exact h.trans (hbd.trans (by nlinarith [le_max_left A L]))
  have hds (x : Boundary D) : ∃ U : Set (Boundary D), IsRegularDisk U ∧
      ball x ((3*M+2)*r)⊆U ∧ U⊆ball x (C*r) := by
    have hs₁ : C*r≤1 := by
      have hh := hrs.trans ((min_le_right ..).trans (min_le_right ..))
      have hh' := (le_div_iff₀ hMp).mp hh
      dsimp only [C]
      rw [div_mul_eq_mul_div]
      apply (div_le_one hc).mpr
      nlinarith [hh']
    obtain ⟨U,hU,hin,hout⟩ := hdisks x (C*r) (mul_pos hC hr) hs₁
    have heq : c*(C*r)=(3*M+2)*r := by dsimp [C]; field_simp
    exact ⟨U,hU,by simpa only [heq] using hin,subset_closure.trans hout⟩
  simpa only [mul_assoc] using CannonLoopApproximation.loop_approximation hr hM hC
    (T:Set (Boundary D)) ((⋃ j, range (F j))∪(T:Set (Boundary D)))
    hcover hcon hj hds f hf

end CannonRelease

end
end
end
end
end
end
end
end

end OAI
