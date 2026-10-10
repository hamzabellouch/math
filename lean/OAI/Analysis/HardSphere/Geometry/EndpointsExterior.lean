import Mathlib
import OAI.Analysis.HardSphere.Geometry.ParentStep
import OAI.Analysis.HardSphere.Geometry.AddedSites

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice
lemma bad_reachable_induce {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) {x y : V} (hx : x∈S) (hy : y∈S)
    (h : (badGraph G S).Reachable x y) :
    (G.induce (↑S)).Reachable ⟨x,hx⟩ ⟨y,hy⟩ := by
  obtain ⟨p⟩ := h
  revert hx
  induction p with
  | nil => intro hx; exact .refl _
  | @cons x z y he p ih =>
    intro hx
    exact (show (G.induce (↑S)).Adj ⟨x,hx⟩ ⟨z,he.2.1⟩ from he.2.2).reachable.trans (ih hy he.2.1)

lemma periodicLift_internalReach {K a : ℕ} (S : Finset (DiscreteTorus K))
    {r x : Vertex} (hx : x∈periodicLift K a S r) :
    withinReach (rangeStep a) (periodicLift K a S r) r x := by
  obtain ⟨_,hp⟩ := hx
  induction hp with
  | refl => exact .refl
  | @tail u v hru huv ih =>
    exact (ih huv.1).tail ⟨⟨huv.1,hru⟩,⟨huv.2.1,hru.tail huv⟩,huv.2.2⟩

lemma exists_bad_lift {K : ℕ} [NeZero K] (hK : 2<K)
    (B : Finset (DiscreteTorus K)) (r : Vertex) (hr : torusProjection K r∈B)
    (hsmall : (badComponent (torusRangeGraph K 1) B (torusProjection K r)).card<K) :
    ∃ C : Finset Vertex,
      (↑C : Set Vertex)=periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r)) r ∧
      r∈C ∧ starConnected (↑C) ∧
      (∀ x∈C, torusProjection K x∈B) ∧
      (∀ c∈C, ∀ x, torusProjection K x∈B → starStep c x → x∈C) := by
  let S := badComponent (torusRangeGraph K 1) B (torusProjection K r)
  have hrS : torusProjection K r∈S := mem_own_badComponent _ _ hr
  obtain ⟨C,hC,_,_⟩ := small_periodic_lifts (a:=1) (by simpa using hK) S
    (by simpa using hsmall) (badComponent_preconnected _ _ _) r hrS
  have hrC : r∈C := by change r∈(↑C:Set Vertex); rw [hC]; exact ⟨hrS,.refl⟩
  refine ⟨C,hC,hrC,?_,?_,?_⟩
  · rw [hC]
    intro x hx y hy
    change withinReach (rangeStep 1) (periodicLift K 1 S r) x y
    exact (withinReach_symm (fun _ _ h ↦ rangeStep_symm h) (periodicLift_internalReach S hx)).trans
      (periodicLift_internalReach S hy)
  · intro x hx
    have hx' : x∈periodicLift K 1 S r := by rw [← hC]; exact hx
    exact badComponent_subset _ _ _ hx'.1
  · intro c hc x hx hcx
    have hc' : c∈periodicLift K 1 S r := by rw [← hC]; exact hc
    have hproj := rangeStep_projection (a:=1) (by simpa using hK) (show rangeStep 1 c x from hcx)
    have hstep : (badGraph (torusRangeGraph K 1) B).Adj (torusProjection K c) (torusProjection K x) :=
      ⟨badComponent_subset _ _ _ hc'.1,hx,hproj⟩
    have hxS : torusProjection K x∈S := (mem_badComponent _ _ _ _).mpr
      ⟨hx,((mem_badComponent _ _ _ _).mp hc'.1).2.trans hstep.reachable⟩
    change x∈(↑C:Set Vertex)
    rw [hC]
    exact ⟨hxS,hc'.2.tail ⟨hc'.1,hxS,hcx⟩⟩

def endpointsExterior {K : ℕ} [NeZero K] (B : Finset (DiscreteTorus K))
    (v w : Vertex) : Prop :=
  ∀ r : Vertex, torusProjection K r∈B → ∀ C : Finset Vertex,
    (↑C : Set Vertex)=periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r)) r →
    v∈exterior C ∧ w∈exterior C

lemma torusRangeGraph_mono {K a b : ℕ} (hab : a≤b) :
    torusRangeGraph K a≤torusRangeGraph K b := by
  intro x y h
  exact ⟨h.1,torusNear_mono hab h.2⟩

lemma badGraph_graphMono {V : Type*} [Fintype V] [DecidableEq V] {G G' : SimpleGraph V}
    (h : G≤G') (B : Finset V) : badGraph G B≤badGraph G' B := by
  intro x y he
  exact ⟨he.1,he.2.1,h he.2.2⟩

def torusNearestGraph (K : ℕ) : SimpleGraph (DiscreteTorus K) where
  Adj x y := x≠y ∧ ∃ u v : Vertex, torusProjection K u=x ∧ torusProjection K v=y ∧ nearestStep u v
  symm := ⟨by
    intro x y h
    obtain ⟨hne,u,v,hu,hv,he⟩ := h
    exact ⟨hne.symm,v,u,hv,hu,nearestStep_symm he⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def nearestProjection {K : ℕ} (hK : 2<K) : nearestGraph →g torusNearestGraph K where
  toFun := torusProjection K
  map_rel' := by
    intro x y h
    exact ⟨short_projection_ne (a:=1) (by simpa using hK) (nearestStep_star h),x,y,rfl,rfl,h⟩

theorem periodic_good_detour {K : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (B : Finset (DiscreteTorus K))
    (hsmall : ∀ z∈B, (badComponent (torusRangeGraph K 1) B z).card<K)
    (Γ : Finset Vertex) {v w : Vertex} (hvΓ : v∈Γ) (hwΓ : w∈Γ)
    (hE : endpointsExterior B v w) (hwalk : withinReach nearestStep (↑Γ) v w) :
    ∃ p : (torusNearestGraph K).Walk (torusProjection K v) (torusProjection K w),
      p.IsPath ∧ ∀ x∈p.support, x∉B ∧
        (x∈Γ.image (torusProjection K) ∨ shellAttachment R B (Γ.image (torusProjection K)) x) := by
  let roots := Γ.filter (fun r ↦ torusProjection K r∈B)
  have hex : ∀ r : roots, ∃ C : Finset Vertex,
      (↑C : Set Vertex)=periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r.val)) r.val ∧
      r.val∈C ∧ starConnected (↑C) ∧
      (∀ x∈C, torusProjection K x∈B) ∧
      (∀ c∈C, ∀ x, torusProjection K x∈B → starStep c x → x∈C) := by
    intro r
    have hr := (Finset.mem_filter.mp r.property).2
    exact exists_bad_lift hK B r.val hr (hsmall _ hr)
  choose C hC using hex
  let Cs : Finset (Finset Vertex) := Finset.univ.image C
  have hCs : ∀ D∈Cs, starConnected (↑D) := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact (hC r).2.2.1
  have hbad : ∀ D∈Cs, (↑D:Set Vertex)⊆(torusProjection K) ⁻¹' (↑B) := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact (hC r).2.2.2.1
  have hmax : ∀ D∈Cs, ∀ c∈D, ∀ x∈(torusProjection K) ⁻¹' (↑B), starStep c x → x∈D := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact (hC r).2.2.2.2
  have hcover : ∀ x∈(↑Γ:Set Vertex), x∈(torusProjection K) ⁻¹' (↑B) → ∃ D∈Cs, x∈D := by
    intro x hx hxB
    let r : roots := ⟨x,Finset.mem_filter.mpr ⟨hx,hxB⟩⟩
    exact ⟨C r,Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩,(hC r).2.1⟩
  have hmeet : ∀ D∈Cs, ∃ x∈(↑Γ:Set Vertex), x∈D := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact ⟨r.val,(Finset.mem_filter.mp r.property).1,(hC r).2.1⟩
  have hends : ∀ D∈Cs, v∈exterior D ∧ w∈exterior D := by
    intro D hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    exact hE r.val (Finset.mem_filter.mp r.property).2 (C r) (hC r).1
  obtain ⟨q,_,hq⟩ := simple_good_detour (↑Γ) ((torusProjection K) ⁻¹' (↑B)) Cs
    hCs hbad hmax hcover hmeet hvΓ hwΓ (fun D hD ↦ (hends D hD).1)
    (fun D hD ↦ (hends D hD).2) hwalk
  let qT := q.map (nearestProjection hK)
  refine ⟨qT.toPath.val,qT.toPath.isPath,?_⟩
  intro x hx
  have hxq : x∈qT.support := qT.support_toPath_subset_support hx
  rw [SimpleGraph.Walk.support_map] at hxq
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hxq
  change torusProjection K y∉B ∧ _
  refine ⟨(hq y hy).1,?_⟩
  rcases (hq y hy).2 with hyΓ|⟨D,hD,_,hyD⟩
  · exact Or.inl (Finset.mem_image.mpr ⟨y,hyΓ,rfl⟩)
  · right
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨_,c,hc,hcy⟩ := hyD
    have hc' : c∈periodicLift K 1 (badComponent (torusRangeGraph K 1) B (torusProjection K r.val)) r.val := by
      rw [← (hC r).1]; exact hc
    have hcr := ((mem_badComponent _ _ _ _).mp hc'.1).2.symm
    have hbig := hcr.mono (badGraph_graphMono (torusRangeGraph_mono (show 1≤R+2 by omega)) B)
    refine ⟨torusProjection K c,(hC r).2.2.2.1 c hc,
      (rangeStep_projection (a:=1) (by simpa using hK) hcy).2,
      torusProjection K r.val,Finset.mem_image.mpr ⟨r.val,(Finset.mem_filter.mp r.property).1,rfl⟩,?_⟩
    exact (mem_badComponent _ _ _ _).mpr ⟨(Finset.mem_filter.mp r.property).2,hbig⟩

end HardSphere.Lattice

end

end OAI
