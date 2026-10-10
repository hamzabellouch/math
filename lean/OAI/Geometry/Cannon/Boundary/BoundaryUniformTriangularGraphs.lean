import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.TraceCard
import OAI.Geometry.Cannon.PlaneTopology.FaceVerticesCard

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
namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc

  CannonFaceIncidence CannonFaceLabels CannonPlaneLinear CannonIncidence CannonPolygonal
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_triangular_graphs (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ M L r₀ : ℝ, 1≤M ∧ 1≤L ∧ 0<r₀ ∧ ∃ N : ℕ,
      ∀ r : ℝ, 0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y≤r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : ℂ → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ (κ : Type) (H : κ → Arc ℂ), Finite κ ∧ Nonempty κ ∧
        Pairwise (fun i j => Compatible (H i) (H j)) ∧
        (∃ Q : Finset (ℂ × ℂ),∀ i,range (H i)⊆⋃ q∈Q,segment ℝ q.1 q.2) ∧
        (T:Set (Boundary D))⊆e '' (⋃ i,range (H i)) ∧
        (∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q})) ∧
        (∀ i,∀ t s : I,dist (e (H i t)) (e (H i s))≤M*r) ∧
        (∀ d,∀ z∈closure (face H d),∀ w∈closure (face H d),dist (e z) (e w)≤L*r) ∧
        (∀ x : Boundary D,Nat.card {i : κ | ∃ t:I,dist (e (H i t)) x<2*M*r}≤N) ∧
        (∀ d : Faces H,∃ i j k : κ,i≠j ∧ j≠k ∧ k≠i ∧
          frontier (face H d)=range (H i)∪range (H j)∪range (H k) ∧
          closure (face H d)=face H d∪(range (H i)∪range (H j)∪range (H k))) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨A,L,rG,hA,hL,hrG,K,J,hgraph⟩ := boundary_uniform_controlled_faces D hδ φ
  let M := max A L
  have hM : 1≤M := hA.trans (le_max_left _ _)
  let R := 2*M+2*L
  have hR : 0<R := by dsimp only [R]; linarith
  obtain ⟨Q₀,C,hQ₀,hC,hpoly⟩ := relative_polynomial_packing D hδ
  obtain ⟨B,hB⟩ := uniform_larger_trace Q₀ C R hpoly hC.le hR
  refine ⟨M,L,min rG (1/(R+1)),hM,hL,lt_min hrG (by positivity),
    (1+12*J)*(1+4*J)*(B*K),?_⟩
  intro r hr hrs T hsep hcover p hpT
  have hrG' : r≤rG := hrs.trans (min_le_left ..)
  have hrR : r≤1/(R+1) := hrs.trans (min_le_right ..)
  have hscale : (R+1)*r≤1 := by
    have hh := (le_div_iff₀ (by linarith : 0<R+1)).mp hrR
    nlinarith
  obtain ⟨e,he,heR,Q,n,hn,F,hF,hFd,hFt,hFJ,hconn,hTV,hFS,hfinite,hsmall,hstructure⟩ :=
    hgraph r hr hrG' T hsep hcover p hpT
  let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let V : Set (Boundary D) := ⋃ i,range (F i)
  have hrange (i : Fin n) : range (F i)⊆range e :=
    (subset_iUnion (fun j => range (F j)) i).trans (hFS.trans (image_subset_range ..))
  let Fc : Fin n → Arc ℂ := fun i => pullChart e he.isEmbedding (F i) (hrange i)
  have hmap (i : Fin n) (t : I) : e (Fc i t)=F i t := map_pullChart e he.isEmbedding (F i) (hrange i) t
  have hFc : Pairwise (fun i j => Compatible (Fc i) (Fc j)) :=
    fun _ _ hij => pullChart_compatible e he.isEmbedding _ _ _ _ (hF hij)
  have hFcQ (i : Fin n) : range (Fc i)⊆⋃ q∈Q,segment ℝ q.1 q.2 := by
    rintro z ⟨t,rfl⟩
    obtain ⟨w,hw,hew⟩ := hFS (mem_iUnion.mpr ⟨i,mem_range_self t⟩)
    exact he.injective (hew.trans (hmap i t).symm) ▸ hw
  have himage : e '' (⋃ i,range (Fc i))=V := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hw
      exact mem_iUnion.mpr ⟨i,t,(hmap i t).symm⟩
    · intro hz
      obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hz
      exact ⟨Fc i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩,hmap i t⟩
  have hconnc : IsPreconnected (⋃ i,range (Fc i)) := by
    apply he.isEmbedding.isInducing.isPreconnected_image.mp
    rw [himage]
    exact hconn.isConnected.isPreconnected
  have hfcSmall (d : Faces Fc) :
      ∀ z∈closure (face Fc d),∀ w∈closure (face Fc d),dist (e z) (e w)≤L*r := by
    apply continuous_closure_diam e he.continuous
    have hc : IsPreconnected (e '' face Fc d) :=
      (CannonFaceIncidence.component_region_connected _ d).isPreconnected.image e he.continuous.continuousOn
    have hs : e '' face Fc d⊆Vᶜ := by
      rintro z ⟨w,hw,rfl⟩ hv
      rw [←himage] at hv
      obtain ⟨u,hu,heu⟩ := hv
      have heq := he.injective heu
      subst u
      exact (region_subset _ ConnectedComponents.mk d hw) hu
    intro z hz w hw
    exact (hsmall _ hc hs (e z) (mem_image_of_mem _ hz) (e w) (mem_image_of_mem _ hw)).le
  have hfcE (i : Fin n) (t s : I) : dist (e (Fc i t)) (e (Fc i s))≤A*r := by
    rw [hmap,hmap]
    exact (dist_le_diam_of_mem (F i).compact_range.isBounded (mem_range_self _) (mem_range_self _)).trans (hFd i)
  let _ : LocallyConnectedSpace ((⋃ i,range (Fc i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (Fc i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (Fc i))ᶜ : Set ℂ)) := inferInstance
  have hfcB (d : Faces Fc) : Nat.card (regionEdges Fc ConnectedComponents.mk d)≤J := by
    obtain ⟨x,hx⟩ := face_nonempty Fc d
    have hs : regionEdges Fc ConnectedComponents.mk d⊆
        {i | (range (F i)∩ball (e x) ((L+1)*r)).Nonempty} := by
      intro i hi
      refine ⟨F i 0,mem_range_self 0,?_⟩
      have hcl := region_edge_in_closure Fc hFc Q hFcQ ConnectedComponents.continuous_coe hi (mem_range_self (0:I))
      have hd := hfcSmall d (Fc i 0) hcl x (subset_closure hx)
      rw [hmap] at hd
      change dist (F i 0) (e x)<(L+1)*r
      nlinarith
    calc
      Nat.card (regionEdges Fc ConnectedComponents.mk d)≤
          Nat.card {i | (range (F i)∩ball (e x) ((L+1)*r)).Nonempty} :=
        Nat.card_le_card_of_injective (Set.inclusion hs) (Set.inclusion_injective hs)
      _=intersectionCount F (ball (e x) ((L+1)*r)) := by
        simp [intersectionCount_eq_card,Nat.card_eq_fintype_card,Fintype.card_subtype]
      _≤J := hFJ (e x)
  obtain ⟨κ,H,hκ,hκn,hH,hHQ,hFH,hHK,hHE,hHD,hHC,hTri⟩ :=
    quantitative_triangular_refinement Fc hFc Q hFcQ hconnc e (L*r) (A*r)
      (mul_nonneg (by linarith) hr.le) hfcSmall hfcE J hfcB
  let _ : Finite κ := hκ
  let _ : Nonempty κ := hκn
  refine ⟨e,he,heR,κ,H,hκ,hκn,hH,hHQ,?_,hHK,?_,hHD,?_,hTri⟩
  · apply hTV.trans
    change V⊆e '' (⋃ i,range (H i))
    rw [←himage]
    exact image_mono hFH
  · intro i t s
    have hm : max (A*r) (L*r)=M*r := by
      exact (max_mul_of_nonneg A L hr.le).symm
    exact hm ▸ hHE i t s
  · intro x
    have hlarge := hB r A hr hA hscale T hsep hcover (fun i => range (F i)) K
      (fun x => by simpa only [traceCard,intersectionCount_eq_card] using hFt x) x
    have hcount : Nat.card {i : Fin n | ∃ t:I,dist (e (Fc i t)) x<2*M*r+2*(L*r)}≤B*K := by
      have heq : 2*M*r+2*(L*r)=R*r := by dsimp only [R]; ring
      simp_rw [heq,hmap]
      have hp : {i : Fin n | ∃ t:I,dist (F i t) x<R*r}=
          {i : Fin n | (range (F i)∩ball x (R*r)).Nonempty} := by
        ext i
        constructor
        · rintro ⟨t,ht⟩
          exact ⟨F i t,mem_range_self t,ht⟩
        · rintro ⟨y,⟨t,rfl⟩,hy⟩
          exact ⟨t,hy⟩
      rw [hp]
      simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,traceCard,Set.mem_ofPred_eq] using hlarge
    exact (hHC x (2*M*r)).trans (Nat.mul_le_mul_left _ hcount)
end CannonRelease

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
