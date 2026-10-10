import Mathlib
import OAI.Geometry.Cannon.Boundary.ExpansionGlobalUpper
import OAI.Geometry.Cannon.PlaneTopology.Lift
import OAI.Geometry.Cannon.PlaneTopology.IntersectionCountEmbedding
import OAI.Geometry.Cannon.PlaneTopology.FiniteSupport
import OAI.Geometry.Cannon.Conformal.SpherePuncturedChart

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
open Set Metric

variable {X : Type*} [MetricSpace X]
theorem net_arc_graph_in_set (Q : ℕ) (C L : ℝ)
    (hp : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C) (hL : 1≤L) :
    ∃ K : ℕ, ∀ (r : ℝ), 0<r → 7*L*r≤1 → ∀ T : Finset X,
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      ∀ S : Set X, (∀ x∈T, ∀ y∈T, x≠y → dist x y<4*r →
        ∃ a : Arc X, a 0=x ∧ a 1=y ∧ diam (range a)≤L*r ∧ range a⊆S) →
      ∃ n : ℕ, ∃ F : Fin n → Arc X,
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ x∈T, ∀ y∈T, x≠y → dist x y<4*r →
           Vertex F x ∧ Vertex F y ∧ ∃ b : Arc X, b 0=x ∧ b 1=y ∧
             range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*L*r) ∧
        (∀ j, diam (range (F j))≤L*r) ∧
        (∀ x, intersectionCount F (ball x (2*L*r))≤K) ∧
        (⋃ j, range (F j))⊆S := by
  classical
  have hLpos : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨K,hK⟩ := CannonPacking.exists_overlap_bound Q C (7*L) 1 hp hC (by positivity) zero_lt_one
  refine ⟨colorBound (K^2+1),?_⟩
  intro r hr hs T hsep S harc
  let P := {p : T×T // p.1≠p.2 ∧ dist p.1.val p.2.val<4*r}
  have hAP (p : P) : ∃ a : Arc X, a 0=p.val.1.val ∧ a 1=p.val.2.val ∧ diam (range a)≤L*r ∧ range a⊆S :=
    harc p.val.1.val p.val.1.property p.val.2.val p.val.2.property
      (fun h => p.property.1 (Subtype.ext h)) p.property.2
  choose A h₀ h₁ hd hAS using hAP
  have hlocal (x : X) : ((Finset.univ : Finset T).filter
      (fun t => dist x t.val≤7*(L*r))).card≤K := by
    have hscale : max (7*L) 1*r≤1 := by rw [max_eq_left (by linarith : (1:ℝ)≤7*L)]; exact hs
    have hsep' : ∀ i∈(Finset.univ : Finset T), ∀ j∈(Finset.univ : Finset T),
        i≠j → 1*r≤dist i.val j.val := by
      intro i _ j _ hij
      simpa only [one_mul] using (hsep i.val i.property j.val j.property
        (fun h => hij (Subtype.ext h)))
    simpa only [mul_assoc] using hK (fun t : T => t.val) Finset.univ x r hr hscale hsep'
  obtain ⟨color,hcolor⟩ := separated_arc_coloring (fun t : T => t.val)
    (fun p : P => p.val.1) (fun p : P => p.val.2)
    (fun i j h => Subtype.ext h) A h₀ h₁ (mul_pos hLpos hr) hd K hlocal
  obtain ⟨n,F,hFc,hFv,hFj,hFd,hFt,hFs⟩ := colored_arc_graph A (K^2+1) color (mul_pos hLpos hr) hd hcolor
  refine ⟨n,F,hFc,?_,hFd,?_,hFs.trans (iUnion_subset hAS)⟩
  · intro x hx y hy hxy hnear
    let p : P := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h),hnear⟩
    have hv := hFv p
    obtain ⟨b,hb₀,hb₁,hbs,hbd⟩ := hFj p
    refine ⟨?_,?_,b,?_,?_,hbs,?_⟩
    · simpa only [h₀,p] using hv.1
    · simpa only [h₁,p] using hv.2
    · exact hb₀.trans (h₀ p)
    · exact hb₁.trans (h₁ p)
    · simpa only [mul_assoc] using hbd
  · simpa only [mul_assoc] using hFt

end CannonEmbeddedArc.Arc

namespace CannonRelease
open Set Metric CannonGraph CannonPacking CannonEmbeddedArc CannonEmbeddedArc.Arc CannonRegularDisk

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_polygonal_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A r₀ : ℝ, 1≤A ∧ 0<r₀ ∧ ∃ K : ℕ, ∀ r : ℝ, 0<r → r≤r₀ →
      ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      ∀ p : Boundary D, p∉T →
      ∃ e : Plane → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ P : Finset (Plane×Plane), ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun i j => Compatible (F i) (F j)) ∧
        (∀ x∈T, ∀ y∈T, x≠y → dist x y<4*r →
          Vertex F x ∧ Vertex F y ∧ ∃ b : Arc (Boundary D), b 0=x ∧ b 1=y ∧
            range b⊆(⋃ j, range (F j)) ∧ diam (range b)≤3*A*r) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        ((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e '' (⋃ q∈P, segment ℝ q.1 q.2) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨c,hc,hc₁,hdisks⟩ := boundary_controlled_regular_disks D hδ φ
  obtain ⟨Q,C,_,hC,hp⟩ := relative_polynomial_packing D hδ
  let A := 8/c
  have hA : 1≤A := by dsimp [A]; apply (le_div_iff₀ hc).mpr; linarith
  have hAp : 0<A := zero_lt_one.trans_le hA
  obtain ⟨K,hK⟩ := net_arc_graph_in_set Q C A hp hC.le hA
  refine ⟨A,1/(7*A),hA,by positivity,K,?_⟩
  intro r hr hrs T hsep p hpT
  have hscale : 7*A*r≤1 := by
    have h := (le_div_iff₀ (by positivity : 0<7*A)).mp hrs
    nlinarith
  have hs : 4*r/c≤1 := by
    apply (div_le_one hc).mpr
    have hh : A*c=8 := by dsimp [A]; field_simp
    nlinarith [mul_le_mul_of_nonneg_right hscale hc.le]
  obtain ⟨e,he,heR⟩ := CannonPolygonal.sphere_punctured_chart φ p
  let J := {q : T×T // q.1≠q.2 ∧ dist q.1.val q.2.val<4*r}
  have hj (j : J) : ∃ a : Arc (Boundary D), a 0=j.val.1.val ∧ a 1=j.val.2.val ∧
      diam (range a)≤A*r ∧ ∃ P : Finset (Plane×Plane),
        range a⊆e '' (⋃ q∈P, segment ℝ q.1 q.2) := by
    let x := j.val.1.val
    let y := j.val.2.val
    obtain ⟨U,hU,hin,hout⟩ := hdisks x (4*r/c) (by positivity) hs
    have heq : c*(4*r/c)=4*r := by field_simp
    have hx : x∈U := hin (by rw [heq]; exact mem_ball_self (by positivity))
    have hy : y∈U := hin (by rw [heq]; change dist y x<4*r; rw [dist_comm]; exact j.property.2)
    have hxp : x≠p := fun h => hpT (h ▸ j.val.1.property)
    have hyp : y≠p := fun h => hpT (h ▸ j.val.2.property)
    have hxy : x≠y := fun h => j.property.1 (Subtype.ext h)
    obtain ⟨a,ha₀,ha₁,has,P,hP⟩ := CannonPolygonal.regular_disk_chart_arc e he p heR hU hx hy hxp hyp hxy
    refine ⟨a,ha₀,ha₁,?_,P,hP⟩
    calc
      diam (range a) ≤ diam (ball x (4*r/c)) := diam_mono (has.trans (subset_closure.trans hout)) (isBounded_ball ..)
      _ ≤ 2*(4*r/c) := diam_ball (by positivity)
      _ = A*r := by dsimp [A]; ring
  choose B hB₀ hB₁ hBd R hBR using hj
  have ht (t : T) : ∃ q : Plane, e q=t.val := by
    have ht' : t.val∈range e := by rw [heR]; exact fun h => hpT ((mem_singleton_iff.mp h) ▸ t.property)
    exact ht'
  choose q hq using ht
  let P := (Finset.univ.biUnion R)∪(Finset.univ.image (fun t : T => (q t,q t)))
  let S := e '' (⋃ z∈P, segment ℝ z.1 z.2)
  have hBS (j : J) : range (B j)⊆S := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hBR j hx
    obtain ⟨s,hs,hzs⟩ := mem_iUnion₂.mp hz
    refine ⟨z,mem_iUnion₂.mpr ⟨s,?_,hzs⟩,rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hs⟩)
  have hTS : (T:Set (Boundary D))⊆S := by
    intro x hx
    let t : T := ⟨x,hx⟩
    refine ⟨q t,mem_iUnion₂.mpr ⟨(q t,q t),?_,left_mem_segment ..⟩,hq t⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)
  obtain ⟨n,F,hFc,hFj,hFd,hFt,hFS⟩ := hK r hr hscale T hsep S (by
    intro x hx y hy hxy hnear
    let j : J := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h),hnear⟩
    exact ⟨B j,hB₀ j,hB₁ j,hBd j,hBS j⟩)
  exact ⟨e,he,heR,P,n,F,hFc,hFj,hFd,hFt,union_subset hFS hTS⟩
end CannonRelease

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_connected_polygonal_loop_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A B r₀ : ℝ, 1≤A ∧ 0<B ∧ 0<r₀ ∧ ∃ K : ℕ,
      ∀ r : ℝ, 0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y≤r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : Plane → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ P : Finset (Plane×Plane), ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        IsPathConnected ((⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
        (((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e '' (⋃ q∈P, segment ℝ q.1 q.2)) ∧
        (∀ (f : C(I,Boundary D)), f 0=f 1 →
          ∃ H : C(I×I,Boundary D), (∀ t, H (0,t)=f t) ∧
            (∀ t, H (1,t)∈(⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
            (∀ s, H (s,0)=H (s,1)) ∧
            (∀ s s' t, dist (H (s,t)) (H (s',t))<B*r)) := by
  let _ := visualMetricSpace D hδ
  let _ : PathConnectedSpace SphereTwo := CannonPaths.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  dsimp only
  obtain ⟨A,rG,hA,hrG,K,hgraph⟩ := boundary_uniform_polygonal_graph D hδ φ
  obtain ⟨L,rA,hL,hrA,harc⟩ := boundary_controlled_embedded_arcs D hδ φ
  obtain ⟨c,hc,_,hdisks⟩ := boundary_controlled_regular_disks D hδ φ
  let M := max A L
  have hM : 1≤M := hA.trans (le_max_left ..)
  have hMp : 0<3*M+2 := by linarith
  let C := (3*M+2)/c
  have hC : 0<C := div_pos hMp hc
  refine ⟨A,2*C,min rG (min rA (c/(3*M+2))),hA,by positivity,
    lt_min hrG (lt_min hrA (div_pos hc hMp)),K,?_⟩
  intro r hr hrs T hsep hcover p hpT
  obtain ⟨e₀,he₀,he₀R,P,n₀,F₀,hFc₀,hFj₀,hFd₀,hFt₀,hFS₀⟩ := hgraph r hr (hrs.trans (min_le_left ..)) T hsep p hpT
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
  have hFS : ((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e₀ '' (⋃ q∈P, segment ℝ q.1 q.2) := by
    apply Subset.trans _ hFS₀
    apply union_subset_union_left
    exact iUnion_subset (fun j => (show range (F₀ (e j)) ⊆ ⋃ i, range (F₀ i) from subset_iUnion (fun i => range (F₀ i)) (e j)))
  refine ⟨e₀,he₀,he₀R,P,n,F,hFc,hFd,hFt,hconn,hFS,?_⟩
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

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc CannonRegularDisk

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_connected_polygonal_complement_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A L r₀ : ℝ, 1≤A ∧ 1≤L ∧ 0<r₀ ∧ ∃ K : ℕ,
      ∀ r : ℝ, 0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y≤r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : Plane → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ P : Finset (Plane×Plane), ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        IsPathConnected ((⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
        (((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e '' (⋃ q∈P, segment ℝ q.1 q.2)) ∧
        (∀ S : Set (Boundary D), IsPreconnected S →
          S⊆((⋃ j, range (F j))∪(T:Set (Boundary D)))ᶜ →
          ∀ x∈S, ∀ y∈S, dist x y<L*r) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨A,B,rG,hA,hB,hrG,K,hgraph⟩ := boundary_uniform_connected_polygonal_loop_graph D hδ φ
  obtain ⟨C,η,hC,hη,hexpand⟩ := boundary_uniform_expanding_homeomorphs D hδ
  obtain ⟨L,hL,hseparate⟩ := CannonWinding.loop_approximation_separates φ hC hB hη hexpand
  have hLp : 0<L := zero_lt_one.trans_le hL
  refine ⟨A,L,min rG (1/L),hA,hL,lt_min hrG (one_div_pos.mpr hLp),K,?_⟩
  intro r hr hrs T hsep hcover p hpT
  obtain ⟨e,he,heR,P,n,F,hFc,hFd,hFt,hconn,hFS,happrox⟩ := hgraph r hr (hrs.trans (min_le_left ..)) T hsep hcover p hpT
  refine ⟨e,he,heR,P,n,F,hFc,hFd,hFt,hconn,hFS,?_⟩
  apply hseparate r hr (hrs.trans (min_le_right ..))
  intro f hf
  obtain ⟨H,hH₀,hH₁,hHc,hHd⟩ := happrox f hf
  let g : C(I,Boundary D) := ⟨fun t => H (1,t),by fun_prop⟩
  refine ⟨g,hHc 1,?_,?_⟩
  · rintro _ ⟨t,rfl⟩
    exact hH₁ t
  · intro t
    change dist (H (1,t)) (f t)<B*r
    rw [←hH₀ t]
    exact hHd 1 0 t

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
