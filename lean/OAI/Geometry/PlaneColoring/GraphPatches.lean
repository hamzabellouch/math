import OAI.Geometry.PlaneColoring.GraphCuts
import OAI.Geometry.PlaneColoring.HoleApproximation

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v
namespace EuclideanFiveColor
/-- Patch a map across separated bad fibers. Only the intervening values need lie in
 a contractible subspace; the map is kept on one closed set and made constant on the other. -/
theorem contractible_patch {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [NormalSpace X] (D : Set Y) [ContractibleSpace D]
    (f : C(X,Y)) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B)
    (hg : ∀x,x∉A → x∉B → f x∈D) :
    ∃a : D, ∃g : C(X,Y), EqOn g (fun _ => a.val) A ∧ EqOn g f B ∧
      ∀x,g x=f x ∨ g x∈D := by
  obtain ⟨t,htB,htA,ht⟩ := exists_continuous_zero_one_of_isClosed hB hA hd.symm
  obtain ⟨a,⟨H⟩⟩ := id_nullhomotopic D
  let S : Fin 3 → Set X := ![{x | t x≤1/3},{x | 1/3≤t x ∧ t x≤2/3},{x | 2/3≤t x}]
  have hS : ∀i,IsClosed (S i) := by
    intro i
    fin_cases i
    · exact isClosed_le t.continuous continuous_const
    · exact (isClosed_le continuous_const t.continuous).inter
        (isClosed_le t.continuous continuous_const)
    · exact isClosed_le continuous_const t.continuous
  have hc : ⋃i,S i=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    by_cases h0 : t x≤1/3
    · exact ⟨0,h0⟩
    by_cases h1 : t x≤2/3
    · exact ⟨1,⟨(not_le.mp h0).le,h1⟩⟩
    · exact ⟨2,(not_le.mp h1).le⟩
  have hgood (x : S 1) : f x.val∈D := by
    apply hg
    · intro hx
      have he : t x.val=1 := htA hx
      have hh : t x.val≤2/3 := x.property.2
      linarith
    · intro hx
      have he : t x.val=0 := htB hx
      have hh : 1/3≤t x.val := x.property.1
      linarith
  have hτmem (x : S 1) : 3*t x.val-1∈unitInterval := by
    constructor
    · linarith [x.property.1]
    · linarith [x.property.2]
  let τ : C(S 1,unitInterval) := ⟨fun x => ⟨3*t x.val-1,hτmem x⟩,
    ((continuous_const.mul (t.continuous.comp continuous_subtype_val)).sub continuous_const).subtype_mk hτmem⟩
  let φ₁ : C(S 1,Y) := ⟨fun x => (H (τ x,⟨f x.val,hgood x⟩)).val,
    continuous_subtype_val.comp (H.continuous.comp (τ.continuous.prodMk
      ((f.continuous.comp continuous_subtype_val).subtype_mk hgood)))⟩
  let φ : ∀i,C(S i,Y) := fun i => Fin.cases (f.restrict (S 0))
    (fun j => Fin.cases φ₁ (fun j => ContinuousMap.const (S j.succ.succ) a.val) j) i
  have h01 (x : X) (h0 : x∈S 0) (h1 : x∈S 1) : φ 0 ⟨x,h0⟩=φ 1 ⟨x,h1⟩ := by
    have he : t x=1/3 := le_antisymm h0 h1.1
    have hτ : τ ⟨x,h1⟩=0 := by apply Subtype.ext; change 3*t x-1=0; rw [he]; norm_num
    change f x=(H (τ ⟨x,h1⟩,⟨f x,hgood ⟨x,h1⟩⟩)).val
    rw [hτ]
    exact congrArg Subtype.val (H.map_zero_left ⟨f x,hgood ⟨x,h1⟩⟩) |>.symm
  have h12 (x : X) (h1 : x∈S 1) (h2 : x∈S 2) : φ 1 ⟨x,h1⟩=φ 2 ⟨x,h2⟩ := by
    have he : t x=2/3 := le_antisymm h1.2 h2
    have hτ : τ ⟨x,h1⟩=1 := by apply Subtype.ext; change 3*t x-1=1; rw [he]; norm_num
    change (H (τ ⟨x,h1⟩,⟨f x,hgood ⟨x,h1⟩⟩)).val=a.val
    rw [hτ]
    exact congrArg Subtype.val (H.map_one_left ⟨f x,hgood ⟨x,h1⟩⟩)
  have hφ : ∀i j x (hi : x∈S i) (hj : x∈S j),φ i ⟨x,hi⟩=φ j ⟨x,hj⟩ := by
    intro i j x hi hj
    fin_cases i <;> fin_cases j
    · rfl
    · exact h01 x hi hj
    · have h0 : t x≤1/3 := hi; have h2 : 2/3≤t x := hj; linarith
    · exact (h01 x hj hi).symm
    · rfl
    · exact h12 x hi hj
    · have h0 : t x≤1/3 := hj; have h2 : 2/3≤t x := hi; linarith
    · exact (h12 x hj hi).symm
    · rfl
  refine ⟨a,closedCoverMap S hS hc φ hφ,?_,?_,?_⟩
  · intro x hx
    have hx2 : x∈S 2 := by change 2/3≤t x; rw [htA hx]; norm_num
    exact closedCoverMap_apply S hS hc φ hφ ⟨x,hx2⟩
  · intro x hx
    have hx0 : x∈S 0 := by change t x≤1/3; rw [htB hx]; norm_num
    exact closedCoverMap_apply S hS hc φ hφ ⟨x,hx0⟩
  · intro x
    obtain ⟨i,hi⟩ := iUnion_eq_univ_iff.mp hc x
    rw [closedCoverMap_apply S hS hc φ hφ ⟨x,hi⟩]
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (H (τ ⟨x,hi⟩,⟨f x,hgood ⟨x,hi⟩⟩)).property
    · exact Or.inr a.property
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v
namespace EuclideanFiveColor
/-- Edges whose midpoint fibers contain a compact continuum joining the two boundaries. -/
def crossingGraph {X : Type u} {V : Type v} [TopologicalSpace X]
    (f : X → V → ℝ) (A B : Set X) : SimpleGraph V where
  Adj i j := i≠j ∧ FiberCrosses f A B (graphEdgePoint i j (1/2))
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm,?_⟩
    have he : graphEdgePoint j i (1/2)=graphEdgePoint i j (1/2) := by
      convert graphEdgePoint_swap j i (1/2) using 1; norm_num
    rw [he]; exact h.2⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩
/-- If the crossing edges form a forest, the boundary map can be patched to a constant
 on the inner closed set, unchanged on the outer closed set. This replaces the graph-word
 and winding detour for the existential interface-cycle producer. -/
theorem graph_forest_patch {X : Type u} {V : Type v} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [Fintype V] [Nonempty V]
    (f : C(X,GraphSpace (⊤ : SimpleGraph V))) {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B)
    (hforest : (crossingGraph (fun x => (f x).val) A B).IsAcyclic) :
    ∃a : GraphSpace (⊤ : SimpleGraph V), ∃g : C(X,GraphSpace (⊤ : SimpleGraph V)),
      EqOn g (fun _ => a) A ∧ EqOn g f B := by
  let G := crossingGraph (fun x => (f x).val) A B
  obtain ⟨T,hGT,_,hT⟩ := SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic
    (show G≤⊤ from le_top) hforest
  let f₀ : C(X,V → ℝ) := ⟨fun x => (f x).val,continuous_subtype_val.comp f.continuous⟩
  let S : Finset (V → ℝ) := ((Finset.univ : Finset (V×V)).filter
    (fun a => a.1≠a.2 ∧ ¬T.Adj a.1 a.2)).image (fun a => graphEdgePoint a.1 a.2 (1/2))
  have hn : ∀b∈S,¬FiberCrosses f₀ A B b := by
    intro b hb
    obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hij
    intro hh
    exact hij.2 (hGT ⟨hij.1,hh⟩)
  obtain ⟨C₀,C₁,hC₀,hC₁,hCd,hAC,hBC,hSC⟩ := finite_fiber_separation f₀ hA hB hd S hn
  let : ContractibleSpace (GraphCutSpace T) := graphCut_contractible hT
  have hg : ∀x,x∉C₀ → x∉C₁ → f₀ x∈graphCutRealization T := by
    intro x hx₀ hx₁
    refine ⟨(f x).property,?_⟩
    intro i j hij hTij he
    have hm : f₀ x∈S := Finset.mem_image.mpr ⟨(i,j),by simp [hij,hTij],he.symm⟩
    rcases hSC hm with hh|hh
    · exact hx₀ hh
    · exact hx₁ hh
  obtain ⟨a,g,hgA,hgB,hgR⟩ := contractible_patch (graphCutRealization T) f₀ hC₀.isClosed hC₁.isClosed hCd hg
  have hgr (x : X) : g x∈graphRealization (⊤ : SimpleGraph V) := by
    rcases hgR x with hh|hh
    · rw [hh]; exact (f x).property
    · exact hh.1
  let g' : C(X,GraphSpace (⊤ : SimpleGraph V)) := ⟨fun x => ⟨g x,hgr x⟩,g.continuous.subtype_mk hgr⟩
  refine ⟨⟨a.val,a.property.1⟩,g',?_,?_⟩
  · intro x hx
    apply Subtype.ext
    exact hgA (hAC hx)
  · intro x hx
    apply Subtype.ext
    exact hgB (hBC hx)
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
def planeAnnulus (x : ℂ) (r R : ℝ) : Set ℂ := Metric.closedBall x R \ Metric.ball x r
lemma planeAnnulus_compact (x : ℂ) (r R : ℝ) : IsCompact (planeAnnulus x r R) :=
  (isCompact_closedBall x R).diff Metric.isOpen_ball
lemma mem_planeAnnulus {x z : ℂ} {r R : ℝ} : z∈planeAnnulus x r R ↔ dist z x≤R ∧ r≤dist z x := by
  simp [planeAnnulus,not_lt]
def annulusInner (x : ℂ) (r R : ℝ) : Set (planeAnnulus x r R) := {z | dist z.val x=r}
def annulusOuter (x : ℂ) (r R : ℝ) : Set (planeAnnulus x r R) := {z | dist z.val x=R}
lemma sphere_mem_annulus {x z : ℂ} {r R : ℝ} (hrR : r≤R) (hz : z∈Metric.sphere x R) :
    z∈planeAnnulus x r R := by
  apply mem_planeAnnulus.mpr
  have hz' : dist z x=R := hz
  rw [hz']
  exact ⟨le_rfl,hrR⟩
/-- A forest crossing graph yields an actual extension of the outer boundary over
its disk. This uses compact fiber separation and tree contraction, not graph words. -/
theorem annulus_forest_extension {V : Type u} [Fintype V] [Nonempty V]
    {x : ℂ} {r R : ℝ} (hrR : r<R)
    (f : C(planeAnnulus x r R,GraphSpace (⊤ : SimpleGraph V)))
    (hforest : (crossingGraph (fun z => (f z).val) (annulusInner x r R) (annulusOuter x r R)).IsAcyclic) :
    ∃g : C(Metric.closedBall x R,GraphSpace (⊤ : SimpleGraph V)),
      ∀z : Metric.sphere x R,g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩=
        f ⟨z.val,sphere_mem_annulus hrR.le z.property⟩ := by
  let : CompactSpace (planeAnnulus x r R) := isCompact_iff_compactSpace.mp (planeAnnulus_compact x r R)
  have hA : IsClosed (annulusInner x r R) := isClosed_eq (continuous_subtype_val.dist continuous_const) continuous_const
  have hB : IsClosed (annulusOuter x r R) := isClosed_eq (continuous_subtype_val.dist continuous_const) continuous_const
  have hd : Disjoint (annulusInner x r R) (annulusOuter x r R) := by
    apply disjoint_left.mpr
    intro z hz hz'
    exact hrR.ne (hz.symm.trans hz')
  obtain ⟨a,g,hgA,hgB⟩ := graph_forest_patch f hA hB hd hforest
  let X := Metric.closedBall x R
  let Z : Bool → Set X := fun b => if b then {z | r≤dist z.val x} else {z | dist z.val x≤r}
  have hZ : ∀b,IsClosed (Z b) := by
    intro b
    cases b
    · exact isClosed_le (continuous_subtype_val.dist continuous_const) continuous_const
    · exact isClosed_le continuous_const (continuous_subtype_val.dist continuous_const)
  have hcov : ⋃b,Z b=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    rcases le_total (dist z.val x) r with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  let g₁ : C(Z true,GraphSpace (⊤ : SimpleGraph V)) :=
    ⟨fun z => g ⟨z.val.val,mem_planeAnnulus.mpr ⟨z.val.property,z.property⟩⟩,
      g.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  let φ : ∀b,C(Z b,GraphSpace (⊤ : SimpleGraph V)) := fun b => Bool.casesOn b (ContinuousMap.const _ a) g₁
  have heq (z : X) (h0 : z∈Z false) (h1 : z∈Z true) : φ false ⟨z,h0⟩=φ true ⟨z,h1⟩ := by
    exact (hgA (show (⟨z.val,mem_planeAnnulus.mpr ⟨z.property,h1⟩⟩ : planeAnnulus x r R)∈annulusInner x r R from
      le_antisymm h0 h1)).symm
  have hφ : ∀i j z (hi : z∈Z i) (hj : z∈Z j),φ i ⟨z,hi⟩=φ j ⟨z,hj⟩ := by
    intro i j z hi hj
    cases i <;> cases j
    · rfl
    · exact heq z hi hj
    · exact (heq z hj hi).symm
    · rfl
  refine ⟨closedCoverMap Z hZ hcov φ hφ,fun z => ?_⟩
  have hz : (⟨z.val,Metric.sphere_subset_closedBall z.property⟩ : X)∈Z true := by
    change r≤dist z.val x
    rw [show dist z.val x=R from z.property]
    exact hrR.le
  rw [closedCoverMap_apply Z hZ hcov φ hφ (i:=true) ⟨⟨z.val,Metric.sphere_subset_closedBall z.property⟩,hz⟩]
  exact hgB z.property
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
lemma finite_centers_separation (L : Finset ℂ) : ∃s>0,∀x∈L,∀y∈L,x≠y → s<dist x y := by
  let P := {p : L×L // p.1≠p.2}
  obtain ⟨s,hs,hsp⟩ := finite_pos_lt (fun p : P => dist p.val.1.val p.val.2.val)
    (fun p => dist_pos.mpr (fun he => p.property (Subtype.ext he)))
  refine ⟨s,hs,fun x hx y hy hxy => ?_⟩
  exact hsp ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h)⟩
def centerDisks (L : Finset ℂ) (R : ℝ) : Finset MarkedDisk := L.image fun x => ⟨x,R,false⟩
lemma mem_centerDisks {L : Finset ℂ} {R : ℝ} {d : MarkedDisk} :
    d∈centerDisks L R ↔ ∃x∈L,d=⟨x,R,false⟩ := by simp [centerDisks,eq_comm]
lemma centerDisks_sum (L : Finset ℂ) (R : ℝ) : (∑d∈centerDisks L R,d.radius)=(L.card:ℝ)*R := by
  rw [centerDisks,Finset.sum_image (fun x _ y _ h => congrArg MarkedDisk.center h)]
  simp
lemma centerDisks_disjoint {L : Finset ℂ} {R : ℝ}
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y) :
    (centerDisks L R : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) := by
  intro a ha b hb hab
  obtain ⟨x,hx,rfl⟩ := mem_centerDisks.mp ha
  obtain ⟨y,hy,rfl⟩ := mem_centerDisks.mp hb
  have hxy : x≠y := by intro he; subst y; exact hab rfl
  apply disjoint_left.mpr
  intro z hz hz'
  have h1 : dist x z≤R := by simpa only [MarkedDisk.closedBall,Metric.mem_closedBall,dist_comm] using hz
  have h2 : dist z y≤R := hz'
  have hh := dist_triangle x z y
  have hh' := hsep x hx y hy hxy
  linarith
lemma mem_center_holes {L : Finset ℂ} {R : ℝ} {z : ℂ} :
    z∈diskHoles (centerDisks L R) ↔ ∃x∈L,dist z x<R := by
  rw [mem_diskHoles]
  constructor
  · rintro ⟨d,hd,hzd⟩
    obtain ⟨x,hx,rfl⟩ := mem_centerDisks.mp hd
    exact ⟨x,hx,hzd⟩
  · rintro ⟨x,hx,hzx⟩
    exact ⟨⟨x,R,false⟩,mem_centerDisks.mpr ⟨x,hx,rfl⟩,hzx⟩
def activeCenters (L : Finset ℂ) : Finset ℂ := L.filter (fun x => dist x 0≤6)
namespace HoleApprox
lemma annulus_in_domain {c : ℂ → Fin 5} {α t R : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) (hR : R<1) (htR : 2*t<R)
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y) {x : ℂ} (hx : x∈activeCenters L) :
    planeAnnulus x (2*t) R⊆Metric.closedBall (0:ℂ) 7 \ coreHoles a.disks := by
  have hx' := Finset.mem_filter.mp hx
  intro z hz
  have hz' := mem_planeAnnulus.mp hz
  constructor
  · change dist z 0≤7
    exact (dist_triangle z x 0).trans (by linarith [hx'.2])
  · intro hh
    obtain ⟨y,hy⟩ := mem_iUnion.mp (a.cores_near hh)
    obtain ⟨hyL,hzy⟩ := mem_iUnion.mp hy
    change dist z y<2*t at hzy
    by_cases he : x=y
    · subst y; linarith [hz'.2]
    · have hh' := hsep x hx'.1 y hyL he
      have htri := dist_triangle x z y
      rw [dist_comm x z] at htri
      linarith [hz'.1]
lemma outside_centers_in_domain {c : ℂ → Fin 5} {α t R : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) (htR : 2*t<R) (ht1 : 2*t<1) :
    Metric.closedBall (0:ℂ) 5 \ diskHoles (centerDisks (activeCenters L) R)⊆
      Metric.closedBall (0:ℂ) 7 \ coreHoles a.disks := by
  intro z hz
  refine ⟨Metric.closedBall_subset_closedBall (by norm_num) hz.1,?_⟩
  intro hh
  obtain ⟨y,hy⟩ := mem_iUnion.mp (a.cores_near hh)
  obtain ⟨hyL,hzy⟩ := mem_iUnion.mp hy
  change dist z y<2*t at hzy
  have hy0 : dist y 0≤6 := calc
    dist y 0≤dist y z+dist z 0 := dist_triangle _ _ _
    _ ≤ 6 := by rw [dist_comm y z]; have hz0 : dist z 0≤5 := hz.1; linarith
  exact hz.2 (mem_center_holes.mpr ⟨y,Finset.mem_filter.mpr ⟨hyL,hy0⟩,hzy.trans htR⟩)
end HoleApprox
end EuclideanFiveColor
end

end OAI
