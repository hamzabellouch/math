import Mathlib
import OAI.Geometry.Cannon.Modulus.CarrierHomeomorph
import OAI.Geometry.Cannon.Boundary.ThreeMarksTwoMetrics

namespace OAI

section
section
section
noncomputable section
namespace CannonRelease
open Set Metric Topology CannonGraph CannonCarrierCharging CannonUniformization

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_normalized_annular_carriers (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ L c : ℝ,1 ≤ L ∧ 0 < c ∧ c ≤ 1 ∧ ∀ {Y κ : Type*},∀ [PseudoMetricSpace Y],
      ∀ A : κ → Set (Boundary D),∀ K : κ → Set Y,
      ∀ f : C(Boundary D,Y),
      (∀ S : Set Y,f ⁻¹' S ⊆
        ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val) →
      ∀ v : Fin 3 → Boundary D,∀ w : Fin 3 → Y,∀ s t : ℝ,
        (∀ i j,i ≠ j → s ≤ dist (v i) (v j)) →
        (∀ i j,i ≠ j → t ≤ dist (w i) (w j)) →
        (∀ i,f (v i)=w i) →
      ∀ (o a₀ b₀ : Boundary D) (r R : ℝ),0 < r → 0 < R → R ≤ s/2 →
        dist o a₀ ≤ r → R ≤ dist o b₀ →
      ∀ a b : ℝ,0 ≤ a → b ≤ t/2 →
        b ≤ dist (f a₀) (f o) → dist (f b₀) (f o) ≤ a →
      ∀ q∈Icc a b,
        ∃ x∈⋃(d : {d : κ // (sphere (f o) q∩K d).Nonempty}),A d.val,
        ∃ y∈⋃(d : {d : κ // (sphere (f o) q∩K d).Nonempty}),A d.val,
          ∀ γ : Path x y,range γ∈annulusFamily o (L*r) (c*R) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨L,c,hL,hc,hc1,hcross⟩:=boundary_annular_metric_carriers D hδ φ
  refine ⟨L,c,hL,hc,hc1,?_⟩
  intro Y κ _ A K f hpre v w s t hv hw hmark o a₀ b₀ r R hr hR hRs ha₀ hb₀
    a b ha hb hfa hfb
  obtain ⟨z,hz,hfz⟩:=CannonFiniteNormalization.normalized_outer_endpoint
    f v w hv hw hmark hRs hb o
  exact hcross A K f hpre o a₀ b₀ z r R hr hR ha₀ hb₀ hz
    (f o) a b (by simpa using ha) hfa hfb hfz
end CannonRelease

end
end
end
end
section
noncomputable section
namespace CannonTileTopology
open Set Topology Metric
open scoped OnePoint

lemma regular_tiles_inter_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : closure (interior A)=A) (hB : closure (interior B)=B)
    (hd : Disjoint (interior A) (interior B)) {x : X} (hxA : x∈A) (hxB : x∈B) :
    x∈frontier A ∩ frontier B := by
  have hda : Disjoint (interior A) B := hB ▸ hd.closure_right isOpen_interior
  have hdb : Disjoint A (interior B) := hA ▸ hd.closure_left isOpen_interior
  exact ⟨⟨subset_closure hxA,fun h=>Set.disjoint_left.mp hda h hxB⟩,
    ⟨subset_closure hxB,fun h=>Set.disjoint_left.mp hdb hxA h⟩⟩

lemma disk_center_tile_incidence {X κ ν : Type*} [TopologicalSpace X]
    (K : κ → Set X) (V : κ → Set ν) (B : ν → Set X) (p : ν → X)
    (hreg : ∀ d,closure (interior (K d))=K d)
    (hd : Pairwise (fun d e=>Disjoint (interior (K d)) (interior (K e))))
    (hfront : ∀ d,frontier (K d)⊆⋃ j∈V d,B j)
    (hsep : ∀ i j,i≠j → p i∉B j)
    (hvertex : ∀ j,∃ d,j∈V d ∧ p j∈K d) :
    ∀ j d,p j∈K d → j∈V d := by
  intro j d hj
  by_contra hn
  obtain ⟨e,hje,hpe⟩:=hvertex j
  have hde : d≠e:=by intro h; subst e; exact hn hje
  have hf:=(regular_tiles_inter_frontier (hreg d) (hreg e) (hd hde) hj hpe).1
  obtain ⟨i,hi,hpi⟩:=mem_iUnion₂.mp (hfront d hf)
  exact hsep j i (fun h=>hn (h ▸ hi)) hpi

lemma compact_trace {K : Set (OnePoint ℂ)} (hc : IsClosed K) (hpole : ∞∉K) :
    IsCompact (((↑) : ℂ → OnePoint ℂ) ⁻¹' K) := by
  have he : (↑) '' (((↑) : ℂ → OnePoint ℂ) ⁻¹' K)=K := by
    apply image_preimage_eq_of_subset
    intro x hx
    exact OnePoint.ne_infty_iff_exists.mp (fun h=>hpole (h ▸ hx))
  have hc' : IsClosed (((↑) : ℂ → OnePoint ℂ) '' (((↑) : ℂ → OnePoint ℂ) ⁻¹' K)) := by rw [he]; exact hc
  exact (OnePoint.isClosed_image_coe.mp hc').2

lemma image_regular {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) {K : Set X} (hk : closure (interior K)=K) :
    closure (interior (f '' K))=f '' K := by
  rw [←f.image_interior,←f.image_closure,hk]

lemma trace_frontier (K : Set (OnePoint ℂ)) :
    frontier (((↑) : ℂ → OnePoint ℂ) ⁻¹' K)=
      ((↑) : ℂ → OnePoint ℂ) ⁻¹' frontier K :=
  (OnePoint.isOpenMap_coe.preimage_frontier_eq_frontier_preimage
    OnePoint.continuous_coe K).symm

lemma trace_regular {K : Set (OnePoint ℂ)} (hk : closure (interior K)=K) :
    closure (interior (((↑) : ℂ → OnePoint ℂ) ⁻¹' K))=
      ((↑) : ℂ → OnePoint ℂ) ⁻¹' K := by
  rw [←OnePoint.isOpenMap_coe.preimage_interior_eq_interior_preimage
      OnePoint.continuous_coe,
    ←OnePoint.isOpenMap_coe.preimage_closure_eq_closure_preimage
      OnePoint.continuous_coe,hk]
end CannonTileTopology

namespace CannonTileTopology
open Set Metric Topology
open scoped OnePoint

lemma coe_image_interior (K : Set ℂ) :
    interior (((↑) : ℂ → OnePoint ℂ) '' K)=((↑) : ℂ → OnePoint ℂ) '' interior K := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨z,hz,rfl⟩:=interior_subset hx
    have h:=OnePoint.isOpenMap_coe.preimage_interior_eq_interior_preimage OnePoint.continuous_coe
      (((↑) : ℂ → OnePoint ℂ) '' K)
    rw [Set.preimage_image_eq _ OnePoint.coe_injective] at h
    exact ⟨z,h ▸ hx,rfl⟩
  · exact OnePoint.isOpenMap_coe.image_interior_subset _

lemma coe_closure_interior {K : Set ℂ} (hc : IsCompact K)
    (hr : closure (interior K)=K) :
    closure (((↑) : ℂ → OnePoint ℂ) '' interior K)=((↑) : ℂ → OnePoint ℂ) '' K := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset) (hc.image OnePoint.continuous_coe).isClosed
  · simpa only [hr] using (image_closure_subset_closure_image (OnePoint.continuous_coe (X := ℂ)) (s := interior K))

lemma coe_regular {K : Set ℂ} (hc : IsCompact K) (hr : closure (interior K)=K) :
    closure (interior (((↑) : ℂ → OnePoint ℂ) '' K))=((↑) : ℂ → OnePoint ℂ) '' K := by
  rw [coe_image_interior,coe_closure_interior hc hr]

lemma coe_frontier {K : Set ℂ} (hc : IsCompact K) :
    frontier (((↑) : ℂ → OnePoint ℂ) '' K)=((↑) : ℂ → OnePoint ℂ) '' frontier K := by
  rw [frontier,frontier,(hc.image OnePoint.continuous_coe).isClosed.closure_eq,
    hc.isClosed.closure_eq,coe_image_interior,Set.image_sdiff OnePoint.coe_injective]

lemma coe_interior_frontier {K : Set ℂ} (hc : IsCompact K)
    (hr : closure (interior K)=K) :
    frontier (((↑) : ℂ → OnePoint ℂ) '' interior K)=((↑) : ℂ → OnePoint ℂ) '' frontier K := by
  rw [frontier,coe_closure_interior hc hr,
    (OnePoint.isOpenMap_coe _ isOpen_interior).interior_eq,
    frontier,hc.isClosed.closure_eq,Set.image_sdiff OnePoint.coe_injective]

lemma segment_two_closedBalls {a b : ℂ} {r s : ℝ}
    (h : dist a b=r+s) : segment ℝ a b⊆closedBall a r∪closedBall b s := by
  intro z hz
  have he:=dist_add_dist_of_mem_segment hz
  rw [h,dist_comm a z] at he
  by_cases hza : dist z a≤r
  · exact Or.inl hza
  · exact Or.inr (show dist z b ≤ s by linarith)
end CannonTileTopology

end
end

end OAI
