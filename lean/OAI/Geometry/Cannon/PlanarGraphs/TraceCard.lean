import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryLocallyConnected
import OAI.Geometry.Cannon.PlaneTopology.PullChartUnionCompl
import OAI.Geometry.Cannon.Topology.ComponentRegionConnected
import OAI.Geometry.Cannon.Topology.Plane

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

namespace CannonIncidence
open Set Metric

variable {X ι : Type*} [MetricSpace X] [Fintype ι]

noncomputable def traceCard (E : ι → Set X) (S : Set X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => (E i∩S).Nonempty)).card

omit [MetricSpace X] in
lemma traceCard_mono (E : ι → Set X) {S T : Set X} (h : S⊆T) :
    traceCard E S≤traceCard E T := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨_,x,hxE,hxS⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hxE,h hxS⟩

omit [MetricSpace X] in
lemma traceCard_finite_cover (E : ι → Set X) (T : Finset X) (U : X → Set X)
    (S : Set X) (hcover : S⊆⋃ x∈T,U x) (K : ℕ)
    (hK : ∀ x∈T, traceCard E (U x)≤K) : traceCard E S≤T.card*K := by
  classical
  let IX (S : Set X) := Finset.univ.filter (fun i => (E i∩S).Nonempty)
  have hsub : IX S⊆T.biUnion (fun x => IX (U x)) := by
    intro i hi
    obtain ⟨y,hyE,hyS⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨x,hx,hyU⟩ := mem_iUnion₂.mp (hcover hyS)
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hyE,hyU⟩⟩
  calc
    traceCard E S=(IX S).card := rfl
    _≤(T.biUnion (fun x => IX (U x))).card := Finset.card_le_card hsub
    _≤∑ x∈T,(IX (U x)).card := Finset.card_biUnion_le
    _≤∑ _x∈T,K := Finset.sum_le_sum (fun x hx => hK x hx)
    _=T.card*K := by simp

theorem uniform_larger_trace (Q : ℕ) (C R : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C) (hR : 0<R) :
    ∃ B : ℕ, ∀ (r A : ℝ), 0<r → 1≤A → (R+1)*r≤1 →
      ∀ T : Finset X, (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : X, ∃ t∈T, dist x t≤r) →
      ∀ {κ : Type*} [Fintype κ], ∀ E : κ → Set X, ∀ K : ℕ, (∀ x, traceCard E (ball x (2*A*r))≤K) →
      ∀ x, traceCard E (ball x (R*r))≤B*K := by
  classical
  obtain ⟨B,hB⟩ := CannonPacking.exists_overlap_bound Q C (R+1) 1 hpack hC (by linarith) zero_lt_one
  refine ⟨B,?_⟩
  intro r A hr hA hscale T hsep hcover κ _ E K hK x
  let T' := T.filter (fun t => dist x t≤(R+1)*r)
  have hTc : T'.card≤B := by
    apply hB id T x r hr
    · simpa [max_eq_left (by linarith : (1:ℝ)≤R+1)] using hscale
    · simpa using hsep
  have hcov : ball x (R*r)⊆⋃ t∈T',ball t (2*A*r) := by
    intro y hy
    obtain ⟨t,ht,hyT⟩ := hcover y
    refine mem_iUnion₂.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,?_⟩,?_⟩
    · have hh := dist_triangle x y t
      have hyx : dist x y<R*r := by simpa only [mem_ball,dist_comm] using hy
      linarith
    · change dist y t<2*A*r
      have hh : 2*r≤2*A*r := by nlinarith
      linarith
  exact (traceCard_finite_cover E T' (fun t => ball t (2*A*r)) _ hcov K
    (fun t _ => hK t)).trans (Nat.mul_le_mul_right K hTc)
end CannonIncidence

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc

  CannonFaceIncidence CannonFaceLabels CannonPlaneLinear CannonIncidence
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_controlled_faces (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A L r₀ : ℝ, 1≤A ∧ 1≤L ∧ 0<r₀ ∧ ∃ K J : ℕ,
      ∀ r : ℝ, 0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y≤r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : ℂ → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ Q : Finset (ℂ × ℂ), ∃ n : ℕ, 0<n ∧ ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun i j => Compatible (F i) (F j)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        (∀ x, intersectionCount F (ball x ((L+1)*r))≤J) ∧
        IsPathConnected (⋃ j,range (F j)) ∧ (T:Set (Boundary D))⊆(⋃ j,range (F j)) ∧
        (⋃ j,range (F j))⊆e '' (⋃ q∈Q,segment ℝ q.1 q.2) ∧
        Finite (ConnectedComponents ((⋃ j,range (F j))ᶜ : Set (Boundary D))) ∧
        (∀ R : Set (Boundary D), IsPreconnected R → R⊆(⋃ j,range (F j))ᶜ →
          ∀ x∈R, ∀ y∈R, dist x y<L*r) ∧
        (let Faces := ConnectedComponents ((⋃ j,range (F j))ᶜ : Set (Boundary D))
         let π : ((⋃ j,range (F j))ᶜ : Set (Boundary D)) → Faces := ConnectedComponents.mk
         ∃ (S : Faces → Set (Fin n)) (labels : Fin n → Bool → Faces),
           (∀ d, closure (region _ π d)=region _ π d∪⋃ i∈S d,range (F i)) ∧
           (∀ d i, i∈S d ↔ d∈range (labels i)) ∧
           (∀ d, Nat.card (S d)≤J)) := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyConnectedSpace (Boundary D) := φ.locallyConnectedSpace
  let _ : PathConnectedSpace SphereTwo := CannonPaths.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  let s : SphereTwo := Classical.choice inferInstance
  let _ : Nontrivial (Boundary D) := ⟨⟨φ.symm s,φ.symm (-s),
    fun h => (ne_neg_of_mem_unit_sphere ℝ s) (φ.symm.injective h)⟩⟩
  obtain ⟨a,b,hab⟩ := exists_pair_ne (Boundary D)
  have hdist : 0<dist a b := dist_pos.mpr hab
  dsimp only
  obtain ⟨A,L,rG,hA,hL,hrG,K,hgraph⟩ := boundary_uniform_finite_face_graph D hδ φ
  obtain ⟨Q₀,C,hQ₀,hC,hpoly⟩ := relative_polynomial_packing D hδ
  obtain ⟨B,hB⟩ := uniform_larger_trace Q₀ C (L+1) hpoly hC.le (by linarith)
  refine ⟨A,L,min rG (min (dist a b/4) (1/(L+2))),hA,hL,
    lt_min hrG (lt_min (by positivity) (by positivity)),K,B*K,?_⟩
  intro r hr hrs T hsep hcover p hpT
  have hrG' : r≤rG := hrs.trans (min_le_left ..)
  have hrD : r≤dist a b/4 := hrs.trans ((min_le_right ..).trans (min_le_left ..))
  have hrL : r≤1/(L+2) := hrs.trans ((min_le_right ..).trans (min_le_right ..))
  have hscale : (L+2)*r≤1 := by have hh := (le_div_iff₀ (by linarith : 0<L+2)).mp hrL; nlinarith
  have hTnt : (T:Set (Boundary D)).Nontrivial := by
    obtain ⟨u,hu,hau⟩ := hcover a
    obtain ⟨v,hv,hbv⟩ := hcover b
    refine ⟨u,hu,v,hv,?_⟩
    intro heq
    subst v
    have hh := dist_triangle a u b
    rw [dist_comm u b] at hh
    linarith
  obtain ⟨e₀,he₀,he₀R,P,n,F,hFc,hFd,hFt,hconn,hFS,hfinite,hsmall⟩ :=
    hgraph r hr hrG' T hsep hcover p hpT
  let V : Set (Boundary D) := ⋃ j,range (F j)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun j => (F j).compact_range.isClosed)
  have hTV : (T:Set (Boundary D))⊆V := CannonConnectedSupport.finite_extras_absorbed
    hV T.finite_toSet hconn.isConnected.isPreconnected (hTnt.mono subset_union_right)
  have heq : V∪(T:Set (Boundary D))=V := union_eq_left.mpr hTV
  change IsPathConnected (V∪(T:Set (Boundary D))) at hconn
  change V∪(T:Set (Boundary D))⊆e₀ '' _ at hFS
  change Finite (ConnectedComponents ((V∪(T:Set (Boundary D)))ᶜ : Set (Boundary D))) at hfinite
  change ∀ R : Set (Boundary D), IsPreconnected R → R⊆(V∪(T:Set (Boundary D)))ᶜ →
    ∀ x∈R, ∀ y∈R, dist x y<L*r at hsmall
  rw [heq] at hconn hFS hfinite hsmall
  have hn : 0<n := by
    by_contra hn
    have hn0 : n=0 := Nat.eq_zero_of_not_pos hn
    obtain ⟨x,hx⟩ := hTnt.nonempty
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hTV hx)
    exact (Nat.not_lt_zero i.val) (hn0 ▸ i.isLt)
  let e : ℂ → Boundary D := e₀ ∘ complexPlaneL
  have he : IsOpenEmbedding e := he₀.comp complexPlaneL.toHomeomorph.isOpenEmbedding
  have heR : range e={p}ᶜ := by rw [show range e=range e₀ from (complexPlaneL.surjective.range_comp e₀),he₀R]
  obtain ⟨Q,hQ⟩ := finite_segments_pull P
  have hVS : V⊆e '' (⋃ q∈Q,segment ℝ q.1 q.2) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hFS hx
    refine ⟨complexPlaneL.symm y,?_,by simp [e,Function.comp_def]⟩
    rw [←hQ]
    simpa using hy
  have hrange (i : Fin n) : range (F i)⊆range e :=
    (subset_iUnion (fun j => range (F j)) i).trans (hVS.trans (image_subset_range ..))
  have hQs (i : Fin n) : e ⁻¹' range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨w,hw,heq⟩ := hVS (mem_iUnion.mpr ⟨i,hz⟩)
    exact he.injective heq ▸ hw
  have hwide (x : Boundary D) : intersectionCount F (ball x ((L+1)*r))≤B*K := by
    have hh := hB r A hr hA (by convert hscale using 1; ring) T hsep hcover
      (fun i => range (F i)) K (fun x => by simpa only [traceCard,intersectionCount_eq_card] using hFt x) x
    simpa only [traceCard,intersectionCount_eq_card] using hh
  let Faces := ConnectedComponents (Vᶜ : Set (Boundary D))
  let _ : DiscreteTopology Faces := complement_components_discrete hV
  let π : (Vᶜ : Set (Boundary D)) → Faces := ConnectedComponents.mk
  have hπ : Continuous π := ConnectedComponents.continuous_coe
  obtain ⟨S,labels,hcl,hlabels⟩ := chart_tame_face_structure e he F hrange hFc Q hQs hπ
  refine ⟨e,he,heR,Q,n,hn,F,hFc,hFd,hFt,hwide,hconn,hTV,hVS,hfinite,hsmall,
    S,labels,hcl,hlabels,?_⟩
  intro d
  have hR := component_region_connected Vᶜ d
  obtain ⟨x,hx⟩ := hR.nonempty
  have hRd : region Vᶜ π d⊆closedBall x (L*r) := by
    intro y hy
    simpa only [mem_closedBall,dist_comm] using (hsmall _ hR.isPreconnected (region_subset Vᶜ π d) x hx y hy).le
  have hclose : closure (region Vᶜ π d)⊆closedBall x (L*r) :=
    closure_minimal hRd isClosed_closedBall
  have hsub : S d⊆{i | (range (F i)∩ball x ((L+1)*r)).Nonempty} := by
    intro i hi
    refine ⟨F i 0,mem_range_self 0,?_⟩
    have hh : F i 0∈closure (region Vᶜ π d) := by
      rw [hcl d]
      exact Or.inr (mem_iUnion₂.mpr ⟨i,hi,mem_range_self 0⟩)
    have hd := hclose hh
    change dist (F i 0) x≤L*r at hd
    change dist (F i 0) x<(L+1)*r
    nlinarith
  calc
    Nat.card (S d)≤Nat.card {i | (range (F i)∩ball x ((L+1)*r)).Nonempty} :=
      Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    _=intersectionCount F (ball x ((L+1)*r)) := by
      simp [intersectionCount_eq_card,Nat.card_eq_fintype_card,Fintype.card_subtype]
    _≤B*K := hwide x
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

end OAI
