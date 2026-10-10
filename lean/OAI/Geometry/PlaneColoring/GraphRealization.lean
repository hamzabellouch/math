import OAI.Geometry.PlaneColoring.CyclicCore
import OAI.Geometry.PlaneColoring.PlanarCovers

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- The directional subsequence in the last paragraph of interface-cycle follows
from connectedness and an outer contact. Compactness of the continuum is not needed. -/
lemma continuum_has_approach {x y : ℂ} {K : Set ℂ} (hK : IsPreconnected K)
    (hx : x∈K) (hy : y∈K) (hne : y≠x) :
    ∃v : ℂ, ‖v‖=1 ∧ Nonempty (ApproachingContinuum x K v) := by
  let ρ : ℝ := dist y x
  have hρ : 0<ρ := dist_pos.mpr hne
  let r : ℕ → ℝ := fun n => ρ/(n+1)
  have hr (n) : 0<r n := div_pos hρ (by positivity)
  have hrle (n) : r n≤ρ := (div_le_iff₀ (by positivity : 0<(n:ℝ)+1)).mpr (by
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    nlinarith)
  have hr0 : Tendsto r atTop (𝓝 0) := by
    simpa only [r,div_eq_mul_inv,mul_zero,one_mul] using
      (tendsto_const_nhds (x:=ρ)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have hq (n) : ∃q∈K,dist q x=r n := by
    have hI := hK.intermediate_value (f:=fun z : ℂ => dist z x) hx hy (continuous_id.dist continuous_const).continuousOn
    apply hI
    exact ⟨by simpa using (hr n).le,hrle n⟩
  choose q hqK hqr using hq
  let w : ℕ → ℂ := fun n => (q n-x)/(r n : ℂ)
  have hwn (n) : ‖w n‖=1 := by
    dsimp [w]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hr n),←dist_eq_norm,hqr]
    exact div_self (ne_of_gt (hr n))
  have hwm (n) : w n∈Metric.sphere (0 : ℂ) 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using hwn n
  obtain ⟨v,hv,φ,hφ,hlim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq hwm
  refine ⟨v,by simpa only [Metric.mem_sphere,dist_zero_right] using hv,?_⟩
  refine ⟨⟨hx,r∘φ,w∘φ,fun n => hr (φ n),hr0.comp hφ.tendsto_atTop,
    fun n => hwn (φ n),hlim,?_⟩⟩
  intro n
  have he : x+(r (φ n) : ℂ)*w (φ n)=q (φ n) := by
    dsimp [w]
    have hn : (r (φ n) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hr _))
    field_simp
    ring
  exact he ▸ hqK (φ n)
end EuclideanFiveColor
end

noncomputable section
open Set
namespace EuclideanFiveColor
/-- The compact contact partition used in the manuscript's annular-crossing proof.
This reuses Mathlib's Hausdorff component quotient and its profinite separation theorem. -/
lemma compact_component_partition {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {I O : Set X} (hI : IsCompact I) (hO : IsCompact O)
    (hno : ∀x∈I, Disjoint (connectedComponent x) O) :
    ∃Z₁ Z₂ : Set X, IsCompact Z₁ ∧ IsCompact Z₂ ∧ Disjoint Z₁ Z₂ ∧
      Z₁∪Z₂=univ ∧ I⊆Z₁ ∧ O⊆Z₂ := by
  let q : X → ConnectedComponents X := ConnectedComponents.mk
  have hq : Continuous q := ConnectedComponents.continuous_coe
  have hid : Disjoint (q '' I) (q '' O) := by
    apply disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have hxy : y∈connectedComponent x := ConnectedComponents.coe_eq_coe'.mp he
    exact Set.disjoint_left.mp (hno x hx) hxy hy
  have hsub : q '' I⊆(q '' O)ᶜ := Set.disjoint_left.mp hid
  obtain ⟨C,hC,hIC,hCO⟩ := exists_clopen_of_closed_subset_open
    (hI.image hq).isClosed (hO.image hq).isClosed.isOpen_compl hsub
  refine ⟨q ⁻¹' C,q ⁻¹' Cᶜ,(hC.isClosed.preimage hq).isCompact,
    (hC.compl.isClosed.preimage hq).isCompact,?_,?_,?_,?_⟩
  · exact disjoint_compl_right.preimage q
  · simp only [←preimage_union,union_compl_self,preimage_univ]
  · intro x hx
    exact hIC ⟨x,hx,rfl⟩
  · intro x hx hxc
    exact hCO hxc ⟨x,hx,rfl⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor
/-- Standard affine vertices. These are the manuscript's probability-simplex coordinates. -/
def graphVertex {V : Type u} (i : V) : V → ℝ := fun j => if j=i then 1 else 0
/-- Affine parameterization of an edge, including its two vertices. -/
def graphEdgePoint {V : Type u} (i j : V) (t : ℝ) : V → ℝ :=
  (1-t) • graphVertex i + t • graphVertex j
/-- The geometric realization of a simple graph in its probability simplex.
The equal-endpoint option includes isolated vertices. -/
def graphRealization {V : Type u} (G : SimpleGraph V) : Set (V → ℝ) :=
  {p | ∃ i j, (i=j ∨ G.Adj i j) ∧ ∃ t ∈ Icc (0:ℝ) 1, p=graphEdgePoint i j t}
abbrev GraphSpace {V : Type u} (G : SimpleGraph V) := ↥(graphRealization G)
lemma graphEdgePoint_apply {V : Type u} (i j k : V) (t : ℝ) :
    graphEdgePoint i j t k = (1-t)*(if k=i then 1 else 0)+t*(if k=j then 1 else 0) := rfl
@[simp] lemma graphEdgePoint_zero {V : Type u} (i j : V) : graphEdgePoint i j 0=graphVertex i := by
  simp [graphEdgePoint]
@[simp] lemma graphEdgePoint_one {V : Type u} (i j : V) : graphEdgePoint i j 1=graphVertex j := by
  simp [graphEdgePoint]
@[simp] lemma graphEdgePoint_self {V : Type u} (i : V) (t : ℝ) : graphEdgePoint i i t=graphVertex i := by
  rw [graphEdgePoint,←add_smul]; simp
lemma graphEdgePoint_swap {V : Type u} (i j : V) (t : ℝ) :
    graphEdgePoint i j t=graphEdgePoint j i (1-t) := by
  simp [graphEdgePoint,add_comm]
lemma continuous_graphEdgePoint {V : Type u} (i j : V) : Continuous (graphEdgePoint i j) := by
  exact ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)
lemma graphVertex_mem {V : Type u} (G : SimpleGraph V) (i : V) : graphVertex i∈graphRealization G :=
  ⟨i,i,Or.inl rfl,0,by norm_num,by simp⟩
lemma graphEdgePoint_mem {V : Type u} {G : SimpleGraph V} {i j : V} (hij : i=j ∨ G.Adj i j)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : graphEdgePoint i j t∈graphRealization G :=
  ⟨i,j,hij,t,ht,rfl⟩
lemma graphRealization_mono {V : Type u} {G H : SimpleGraph V} (h : G≤H) :
    graphRealization G⊆graphRealization H := by
  rintro p ⟨i,j,hij,t,ht,rfl⟩
  exact ⟨i,j,hij.imp id (fun hh => h hh),t,ht,rfl⟩
lemma graphRealization_nonneg {V : Type u} {G : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization G) (i : V) : 0≤p i := by
  obtain ⟨a,b,_,t,ht,rfl⟩ := hp
  rw [graphEdgePoint_apply]
  split_ifs <;> nlinarith [ht.1,ht.2]
lemma graphRealization_sum {V : Type u} [Fintype V] {G : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization G) : ∑ i,p i=1 := by
  obtain ⟨a,b,_,t,_,rfl⟩ := hp
  simp [graphEdgePoint,graphVertex,Finset.sum_add_distrib]
lemma graphRealization_compact {V : Type u} [Finite V] (G : SimpleGraph V) :
    IsCompact (graphRealization G) := by
  have he : graphRealization G = ⋃ (i : V) (j : V) (_ : i=j ∨ G.Adj i j),
      graphEdgePoint i j '' Icc (0:ℝ) 1 := by
    ext p
    simp only [mem_iUnion,mem_image,graphRealization,mem_ofPred_eq]
    constructor
    · rintro ⟨i,j,hij,t,ht,rfl⟩; exact ⟨i,j,hij,t,ht,rfl⟩
    · rintro ⟨i,j,hij,t,ht,rfl⟩; exact ⟨i,j,hij,t,ht,rfl⟩
  rw [he]
  exact isCompact_iUnion fun i => isCompact_iUnion fun j => isCompact_iUnion fun _ =>
    isCompact_Icc.image (continuous_graphEdgePoint i j)
lemma graphRealization_closed {V : Type u} [Finite V] (G : SimpleGraph V) :
    IsClosed (graphRealization G) := (graphRealization_compact G).isClosed
instance graphSpace_compact {V : Type u} [Finite V] (G : SimpleGraph V) : CompactSpace (GraphSpace G) :=
  isCompact_iff_compactSpace.mp (graphRealization_compact G)
lemma graphRealization_singleton {V : Type u} [Subsingleton V] (G : SimpleGraph V) (a : V) :
    graphRealization G={graphVertex a} := by
  ext p
  constructor
  · rintro ⟨i,j,_,t,_,rfl⟩
    simp [Subsingleton.elim i a,Subsingleton.elim j a]
  · rintro rfl
    exact graphVertex_mem G a
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor
lemma graphRealization_of_two_support {V : Type u} [Fintype V]
    {G : SimpleGraph V} {p : V → ℝ} (hn : ∀i,0≤p i) (hs : ∑i,p i=1)
    {a b : V} (hab : a=b ∨ G.Adj a b) (hsupp : ∀j,j≠a → j≠b → p j=0) :
    p∈graphRealization G := by
  by_cases he : a=b
  · subst b
    have ha : p a=1 := by
      have hh : ∑i,p i=p a := Finset.sum_eq_single a (fun i _ hi => hsupp i hi hi) (by simp)
      linarith
    have hp : p=graphVertex a := by
      funext i
      by_cases hi : i=a
      · subst i; simp [graphVertex,ha]
      · simp [graphVertex,hi,hsupp i hi hi]
    rw [hp]; exact graphVertex_mem _ _
  · have he' : b≠a := Ne.symm he
    have hs' : p a+p b=1 := by
      have hh : ∑i∈({a,b} : Finset V),p i=∑i,p i := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
        exact hsupp i hi.1 hi.2
      simpa [he] using hh.trans hs
    refine ⟨a,b,hab,p b,⟨hn _,by linarith [hn a]⟩,?_⟩
    funext i
    rw [graphEdgePoint_apply]
    by_cases hi : i=a
    · subst i; simp [he]; linarith
    · by_cases hj : i=b
      · subst i; simp [he']
      · simp [hi,hj,hsupp i hi hj]

/-- A simplex vector whose positive labels form a clique in a forest is genuinely
in that forest's affine realization, rather than just in the complete graph. -/
theorem simplex_mem_forest {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) {p : V → ℝ} (hn : ∀i,0≤p i) (hs : ∑i,p i=1)
    (hcl : ∀i j,i≠j → 0<p i → 0<p j → G.Adj i j) : p∈graphRealization G := by
  let S : Finset V := Finset.univ.filter fun i => p i≠0
  have hmem (i : V) : i∈S ↔ 0<p i := by simp [S,lt_iff_le_and_ne,hn i,ne_comm]
  have hsum : ∑i∈S,p i=1 := by
    have he : ∑i∈S,p i=∑i,p i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      simpa [S] using hi
    exact he.trans hs
  have hne : S.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at hsum
    norm_num at hsum
  have hcard : S.card≤2 := by
    by_contra hh
    have h3 : 3≤S.card := by omega
    obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq h3
    apply hG.cliqueFree (le_refl 3) T
    refine ⟨?_,hT⟩
    intro i hi j hj hij
    exact hcl i j hij ((hmem i).mp (hTS hi)) ((hmem j).mp (hTS hj))
  by_cases h1 : S.card=1
  · obtain ⟨a,hSa⟩ := Finset.card_eq_one.mp h1
    apply graphRealization_of_two_support hn hs (G:=G) (a:=a) (b:=a) (Or.inl rfl)
    intro j hj _
    by_contra hp
    have hm : j∈S := by simp [S,hp]
    rw [hSa,Finset.mem_singleton] at hm
    exact hj hm
  · have h2 : S.card=2 := by have := hne.card_pos; omega
    obtain ⟨a,b,hab,hS⟩ := Finset.card_eq_two.mp h2
    have ha : 0<p a := (hmem _).mp (by rw [hS]; simp)
    have hb : 0<p b := (hmem _).mp (by rw [hS]; simp)
    apply graphRealization_of_two_support hn hs (Or.inr (hcl a b hab ha hb))
    intro j hja hjb
    by_contra hp
    have hm : j∈S := by simp [S,hp]
    rw [hS] at hm
    simp [hja,hjb] at hm
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology MeasureTheory
namespace EuclideanFiveColor
/-- The manuscript's thresholded and renormalized disk average (equation 22). -/
def thresholdWeight (c : ℂ → Fin 5) (ε α : ℝ) (q : ℂ) (i : Fin 5) : ℝ :=
  max (diskAverage c ε i q-α) 0
def thresholdTotal (c : ℂ → Fin 5) (ε α : ℝ) (q : ℂ) : ℝ :=
  ∑i,thresholdWeight c ε α q i
def thresholdMap (c : ℂ → Fin 5) (ε α : ℝ) (q : ℂ) (i : Fin 5) : ℝ :=
  thresholdWeight c ε α q i / thresholdTotal c ε α q
lemma thresholdTotal_pos {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) : 0<thresholdTotal c ε α q := by
  have hs := diskAverage_sum hc hε q
  have hh : 1-5*α ≤ thresholdTotal c ε α q := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)))
      (fun i _ => le_max_left (diskAverage c ε i q-α) 0)
    simpa [thresholdTotal,thresholdWeight,Finset.sum_sub_distrib,hs] using hh
  linarith
lemma thresholdMap_nonneg {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) (i : Fin 5) : 0≤thresholdMap c ε α q i :=
  div_nonneg (le_max_right _ _) (thresholdTotal_pos hc hε hα q).le
lemma thresholdMap_sum {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) : ∑i,thresholdMap c ε α q i=1 := by
  unfold thresholdMap
  rw [←Finset.sum_div]
  exact div_self (thresholdTotal_pos hc hε hα q).ne'
lemma thresholdMap_pos {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) (i : Fin 5) :
    0<thresholdMap c ε α q i ↔ α<diskAverage c ε i q := by
  rw [thresholdMap,div_pos_iff_of_pos_right (thresholdTotal_pos hc hε hα q)]
  simp [thresholdWeight]
lemma continuous_thresholdMap {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) : Continuous (thresholdMap c ε α) := by
  have hw (i : Fin 5) : Continuous (fun q => thresholdWeight c ε α q i) :=
    ((diskAverage_lipschitz hc hε i).continuous.sub continuous_const).max continuous_const
  have ht : Continuous (thresholdTotal c ε α) := continuous_finsetSum _ (fun i _ => hw i)
  exact continuous_pi fun i => (hw i).div ht (fun q => (thresholdTotal_pos hc hε hα q).ne')
lemma thresholdMap_mem_forest {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) {G : SimpleGraph (Fin 5)} (hG : G.IsAcyclic)
    (hb : ∀i j,i≠j → α<diskAverage c ε i q → α<diskAverage c ε j q → G.Adj i j) :
    thresholdMap c ε α q∈graphRealization G := by
  apply simplex_mem_forest hG (thresholdMap_nonneg hc hε hα q) (thresholdMap_sum hc hε hα q)
  intro i j hij hi hj
  exact hb i j hij ((thresholdMap_pos hc hε hα q i).mp hi) ((thresholdMap_pos hc hε hα q j).mp hj)
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma finite_pos_lt {ι : Type*} [Finite ι] (R : ι → ℝ) (hR : ∀i,0<R i) :
    ∃s : ℝ,0<s ∧ ∀i,s<R i := by
  have hh : ∀ᶠ s : ℝ in 𝓝 0,∀i,s<R i := Filter.eventually_all.mpr fun i => gt_mem_nhds (hR i)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨δ/2,half_pos hδ,hd ?_⟩
  change dist (δ/2) (0:ℝ)<δ
  rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hδ)]
  exact half_lt_self hδ
lemma finite_small_scale {ι : Type*} [Finite ι] (P : ι → ℝ → Prop)
    (h : ∀i,∃δ>0,∀ε,0<ε → ε<δ → P i ε) : ∃δ>0,∀ε,0<ε → ε<δ → ∀i,P i ε := by
  choose δ hδ hd using h
  obtain ⟨s,hs,hsi⟩ := finite_pos_lt δ hδ
  exact ⟨s,hs,fun ε hε hεs i => hd i ε hε (hεs.trans (hsi i))⟩

/-- A genuine local forest chart; its exception disks have arbitrarily small total
radius at sufficiently small averaging scale. -/
theorem forest_chart {c : ℂ → Fin 5} (hc : Measurable c) {α : ℝ}
    (hα : 0<α) (hα' : α<1/5) (x : ℂ) (hf : (transitionGraph c x).IsAcyclic) :
    ∃s>0,∀η>0,∃δ>0,∀ε,0<ε → ε<δ → ∃C : Finset ℂ,
      (C.card:ℝ)*(α*ε/4)<η ∧ ∀q∈Metric.ball x s,
      q∉⋃z∈C,Metric.ball z (α*ε/4) → thresholdMap c ε α q∈graphRealization (transitionGraph c x) := by
  have hall : ∀p : Fin 5 × Fin 5,∃R>0, p.1≠p.2 → ¬TransitionEdge c p.1 p.2 x →
      ∀s<R,∀η>0,∃δ>0,∀ε,0<ε → ε<δ → ∃C : Finset ℂ,
        (∀q∈Metric.ball x s,α<diskAverage c ε p.1 q → α<diskAverage c ε p.2 q →
          ∃z∈C,q∈Metric.ball z (α*ε/4)) ∧ (C.card:ℝ)*(α*ε/4)<η := by
    intro p
    by_cases hp : p.1≠p.2 ∧ ¬TransitionEdge c p.1 p.2 x
    · obtain ⟨R,hR,hcov⟩ := missing_edge_disk_cover hc hp.1 hp.2
      exact ⟨R,hR,fun _ _ s hs η hη => hcov s hs α hα η hη⟩
    · exact ⟨1,by norm_num,fun h₁ h₂ => False.elim (hp ⟨h₁,h₂⟩)⟩
  choose R hR hcov using hall
  obtain ⟨s,hs,hsR⟩ := finite_pos_lt R hR
  refine ⟨s,hs,fun η hη => ?_⟩
  let P (p : Fin 5 × Fin 5) (ε : ℝ) : Prop := ∃C : Finset ℂ,
    (C.card:ℝ)*(α*ε/4)<η/25 ∧ (p.1≠p.2 → ¬TransitionEdge c p.1 p.2 x →
      ∀q∈Metric.ball x s,α<diskAverage c ε p.1 q → α<diskAverage c ε p.2 q →
        ∃z∈C,q∈Metric.ball z (α*ε/4))
  have hP : ∀p,∃δ>0,∀ε,0<ε → ε<δ → P p ε := by
    intro p
    by_cases hp : p.1≠p.2 ∧ ¬TransitionEdge c p.1 p.2 x
    · obtain ⟨δ,hδ,hd⟩ := hcov p hp.1 hp.2 s (hsR p) (η/25) (by positivity)
      refine ⟨δ,hδ,fun ε hε hεδ => ?_⟩
      obtain ⟨C,hC,hCr⟩ := hd ε hε hεδ
      exact ⟨C,hCr,fun _ _ => hC⟩
    · refine ⟨1,by norm_num,fun ε _ _ => ⟨∅,by simpa using (show 0<η/25 by positivity),?_⟩⟩
      exact fun h₁ h₂ => False.elim (hp ⟨h₁,h₂⟩)
  obtain ⟨δ,hδ,hd⟩ := finite_small_scale P hP
  refine ⟨δ,hδ,fun ε hε hεδ => ?_⟩
  choose C hCr hC using hd ε hε hεδ
  let T := Finset.univ.biUnion C
  have hr : 0≤α*ε/4 := by positivity
  refine ⟨T,?_,?_⟩
  · have hcard : (T.card:ℝ)≤∑p : Fin 5 × Fin 5,((C p).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := C))
    have hsum : (∑p : Fin 5 × Fin 5,((C p).card:ℝ)*(α*ε/4))<∑_p : Fin 5 × Fin 5,η/25 :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun p _ => hCr p)
    have hb := mul_le_mul_of_nonneg_right hcard hr
    rw [Finset.sum_mul] at hb
    have hsum' : (∑p : Fin 5 × Fin 5,((C p).card:ℝ)*(α*ε/4))<25*(η/25) := by simpa using hsum
    exact hb.trans_lt (by linarith [hsum'])
  · intro q hq hqT
    apply thresholdMap_mem_forest hc hε hα' q hf
    intro i j hij hi hj
    by_contra he
    obtain ⟨z,hz,hqz⟩ := hC (i,j) hij he q hq hi hj
    apply hqT
    exact mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_univ _,hz⟩,hqz⟩⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Compact local forest control with one Lebesgue radius, chosen before the hole
budget and the disk-average scale. The resulting forest controls the WHOLE nearby
ball off the common exception disks, not merely the compact set. -/
theorem compact_forest_charts {c : ℂ → Fin 5} (hc : Measurable c) {α : ℝ}
    (hα : 0<α) (hα' : α<1/5) (M : Set ℂ) (hM : IsCompact M)
    (hf : ∀x∈M,(transitionGraph c x).IsAcyclic) :
    ∃l>0,∀η>0,∃δ>0,∀ε,0<ε → ε<δ → ∃C : Finset ℂ,
      (C.card:ℝ)*(α*ε/4)<η ∧ ∀a∈M,∃G : SimpleGraph (Fin 5),G.IsAcyclic ∧
      ∀q∈Metric.ball a l,q∉⋃z∈C,Metric.ball z (α*ε/4) → thresholdMap c ε α q∈graphRealization G := by
  choose s hs hchart using fun x : M => forest_chart hc hα hα' x.val (hf x.val x.property)
  have hcover : M⊆⋃x : M,Metric.ball x.val (s x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hs _)⟩
  obtain ⟨S,hS⟩ := hM.elim_finite_subcover (fun x : M => Metric.ball x.val (s x))
    (fun _ => Metric.isOpen_ball) hcover
  have hS' : M⊆⋃x : S,Metric.ball x.val.val (s x.val) := by
    intro x hx
    obtain ⟨a,ha⟩ := mem_iUnion.mp (hS hx)
    obtain ⟨haS,hxa⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨⟨a,haS⟩,hxa⟩
  obtain ⟨l,hl,hleb⟩ := lebesgue_number_lemma_of_metric hM (fun _ => Metric.isOpen_ball) hS'
  refine ⟨l,hl,fun η hη => ?_⟩
  let β := η/((S.card:ℝ)+1)
  have hβ : 0<β := div_pos hη (by positivity)
  let P (x : S) (ε : ℝ) : Prop := ∃C : Finset ℂ,
    (C.card:ℝ)*(α*ε/4)<β ∧ ∀q∈Metric.ball x.val.val (s x.val),
      q∉⋃z∈C,Metric.ball z (α*ε/4) → thresholdMap c ε α q∈graphRealization (transitionGraph c x.val.val)
  obtain ⟨δ,hδ,hd⟩ := finite_small_scale P (fun x => hchart x.val β hβ)
  refine ⟨δ,hδ,fun ε hε hεδ => ?_⟩
  choose C hCr hC using hd ε hε hεδ
  let T := Finset.univ.biUnion C
  refine ⟨T,?_,?_⟩
  · have hcard : (T.card:ℝ)≤∑p : S,((C p).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := C))
    have hb := mul_le_mul_of_nonneg_right hcard (show 0≤α*ε/4 by positivity)
    rw [Finset.sum_mul] at hb
    have hsum := Finset.sum_le_sum (s:=(Finset.univ : Finset S)) (fun p _ => (hCr p).le)
    have hsum' : (∑p:S,((C p).card:ℝ)*(α*ε/4))≤(S.card:ℝ)*β := by simpa using hsum
    have hβeq : β*((S.card:ℝ)+1)=η := div_mul_cancel₀ η (by positivity)
    exact hb.trans hsum' |>.trans_lt (by nlinarith)
  · intro a ha
    obtain ⟨x,hx⟩ := hleb a ha
    refine ⟨transitionGraph c x.val.val,hf x.val.val x.val.property,fun q hq hqT => ?_⟩
    apply hC x q (hx hq)
    intro hh
    obtain ⟨z,hz⟩ := mem_iUnion.mp hh
    obtain ⟨hzC,hqz⟩ := mem_iUnion.mp hz
    exact hqT (mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,hzC⟩,hqz⟩⟩)
end EuclideanFiveColor
end

end OAI
