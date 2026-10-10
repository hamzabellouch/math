import OAI.Geometry.PlaneColoring.DiskExtension

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma graphEdgePoint_index {V : Type u} {i j k : V} {t : ℝ}
    (h : graphEdgePoint i j t k ≠ 0) : k=i ∨ k=j := by
  by_contra hh
  simp only [not_or] at hh
  exact h (by simp [graphEdgePoint_apply,hh.1,hh.2])
lemma graphRealization_positive_adj {V : Type u} {G : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization G) {i j : V} (hne : i≠j) (hi : 0<p i) (hj : 0<p j) : G.Adj i j := by
  obtain ⟨a,b,hab,t,ht,rfl⟩ := hp
  have ha := graphEdgePoint_index (ne_of_gt hi)
  have hb := graphEdgePoint_index (ne_of_gt hj)
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · exact (hne rfl).elim
  · exact hab.resolve_left hne
  · exact (hab.resolve_left hne.symm).symm
  · exact (hne rfl).elim
lemma graphRealization_pair_le {V : Type u} {G : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization G) {i j : V} (hne : i≠j) : p i+p j≤1 := by
  obtain ⟨a,b,hab,t,ht,rfl⟩ := hp
  simp only [graphEdgePoint_apply]
  split_ifs <;> subst_vars <;> first | contradiction | nlinarith [ht.1,ht.2]

def graphCutRealization {V : Type u} (T : SimpleGraph V) : Set (V → ℝ) :=
  {p | p∈graphRealization (⊤ : SimpleGraph V) ∧ ∀ i j, i≠j → ¬T.Adj i j →
    p≠graphEdgePoint i j (1/2)}
abbrev GraphCutSpace {V : Type u} (T : SimpleGraph V) := ↥(graphCutRealization T)
lemma graphRealization_subset_cut {V : Type u} (T : SimpleGraph V) :
    graphRealization T⊆graphCutRealization T := by
  intro p hp
  refine ⟨graphRealization_mono le_top hp,?_⟩
  intro i j hne hn he
  apply hn
  apply graphRealization_positive_adj hp hne
  · rw [he]; norm_num [graphEdgePoint_apply,hne,hne.symm]
  · rw [he]; norm_num [graphEdgePoint_apply,hne,hne.symm]
lemma graphCut_dominant {V : Type u} {T : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphCutRealization T) (hn : p∉graphRealization T) : ∃i,1/2<p i := by
  obtain ⟨i,j,hij,t,ht,he⟩ := hp.1
  have hne : i≠j := by
    intro h; apply hn; exact ⟨i,j,Or.inl h,t,ht,he⟩
  have hadj : ¬T.Adj i j := by
    intro h; apply hn; exact ⟨i,j,Or.inr h,t,ht,he⟩
  have htm : t≠1/2 := by intro h; exact hp.2 i j hne hadj (he.trans (by rw [h]))
  rcases lt_or_gt_of_ne htm with hl|hr
  · refine ⟨i,?_⟩; rw [he]; simp [graphEdgePoint_apply,hne]; linarith
  · refine ⟨j,?_⟩; rw [he]; simpa [graphEdgePoint_apply,hne.symm] using hr
lemma graphCut_dominant_unique {V : Type u} {T : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphCutRealization T) {i j : V} (hi : 1/2<p i) (hj : 1/2<p j) : i=j := by
  by_contra hne
  have hh := graphRealization_pair_le hp.1 hne
  linarith

def graphCutRetract {V : Type u} (T : SimpleGraph V) (p : GraphCutSpace T) : V → ℝ :=
  if h : p.val∈graphRealization T then p.val else graphVertex (graphCut_dominant p.property h).choose
lemma graphCutRetract_tree {V : Type u} {T : SimpleGraph V} (p : GraphCutSpace T)
    (hp : p.val∈graphRealization T) : graphCutRetract T p=p.val := by
  simp [graphCutRetract,hp]
lemma graphCutRetract_dominant {V : Type u} {T : SimpleGraph V} (p : GraphCutSpace T)
    (hp : p.val∉graphRealization T) {i : V} (hi : 1/2<p.val i) : graphCutRetract T p=graphVertex i := by
  rw [graphCutRetract,dite_eq_right hp]
  congr 1
  exact graphCut_dominant_unique p.property (graphCut_dominant p.property hp).choose_spec hi
lemma graphCutRetract_mem {V : Type u} (T : SimpleGraph V) (p : GraphCutSpace T) :
    graphCutRetract T p∈graphRealization T := by
  unfold graphCutRetract
  split
  · assumption
  · exact graphVertex_mem _ _
/-- The closed half of a deleted edge, viewed inside the cut graph. -/
def graphCutStub {V : Type u} (T : SimpleGraph V) (i j : V) : Set (GraphCutSpace T) :=
  {p | i≠j ∧ ¬T.Adj i j ∧ p.val∈graphEdgePoint i j '' Icc (0:ℝ) (1/2)}
lemma graphCutStub_retract {V : Type u} {T : SimpleGraph V} {i j : V}
    {p : GraphCutSpace T} (hp : p∈graphCutStub T i j) : graphCutRetract T p=graphVertex i := by
  obtain ⟨hne,hadj,t,ht,he⟩ := hp
  have he' := he.symm
  have htm : t<1/2 := lt_of_le_of_ne ht.2 (by
    intro h; exact p.property.2 i j hne hadj (he'.trans (by rw [h])))
  by_cases hT : p.val∈graphRealization T
  · rw [graphCutRetract_tree p hT]
    have ht0 : t=0 := by
      by_contra hh
      have hp1 : 0<p.val i := by rw [he']; simp [graphEdgePoint_apply,hne]; linarith
      have hp2 : 0<p.val j := by rw [he']; simp [graphEdgePoint_apply,hne.symm]; exact lt_of_le_of_ne ht.1 (Ne.symm hh)
      exact hadj (graphRealization_positive_adj hT hne hp1 hp2)
    rw [he',ht0,graphEdgePoint_zero]
  · apply graphCutRetract_dominant p hT
    rw [he']; simp [graphEdgePoint_apply,hne]; linarith
lemma graphCut_cover {V : Type u} {T : SimpleGraph V} (p : GraphCutSpace T) :
    p.val∈graphRealization T ∨ ∃i j,p∈graphCutStub T i j := by
  by_cases h : p.val∈graphRealization T
  · exact Or.inl h
  right
  obtain ⟨i,j,hij,t,ht,he⟩ := p.property.1
  have hne : i≠j := by intro hh; exact h ⟨i,j,Or.inl hh,t,ht,he⟩
  have hadj : ¬T.Adj i j := by intro hh; exact h ⟨i,j,Or.inr hh,t,ht,he⟩
  by_cases ht' : t≤1/2
  · exact ⟨i,j,hne,hadj,t,⟨ht.1,ht'⟩,he.symm⟩
  · refine ⟨j,i,hne.symm,fun hh => hadj hh.symm,1-t,⟨by linarith [ht.2],by linarith⟩,?_⟩
    exact (graphEdgePoint_swap i j t).symm.trans he.symm
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma graphCutStub_closed {V : Type u} {T : SimpleGraph V} (i j : V) :
    IsClosed (graphCutStub T i j) := by
  change IsClosed ({p : GraphCutSpace T | i≠j} ∩
    ({p : GraphCutSpace T | ¬T.Adj i j} ∩ Subtype.val ⁻¹' (graphEdgePoint i j '' Icc (0:ℝ) (1/2))))
  exact isClosed_const.inter (isClosed_const.inter ((isCompact_Icc.image (continuous_graphEdgePoint i j)).isClosed.preimage
    continuous_subtype_val))
lemma continuous_graphCutRetract {V : Type u} [Finite V] (T : SimpleGraph V) :
    Continuous (graphCutRetract T) := by
  let S : Option (V × V) → Set (GraphCutSpace T) := fun a => match a with
    | none => Subtype.val ⁻¹' graphRealization T
    | some (i,j) => graphCutStub T i j
  have hcov : ⋃a,S a=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro p
    rcases graphCut_cover p with hp|⟨i,j,hp⟩
    · exact ⟨none,hp⟩
    · exact ⟨some (i,j),hp⟩
  apply (locallyFinite_of_finite S).continuous hcov
  · intro a
    cases a with
    | none => exact (graphRealization_closed T).preimage continuous_subtype_val
    | some a => exact graphCutStub_closed a.1 a.2
  · intro a
    cases a with
    | none => exact continuous_subtype_val.continuousOn.congr (fun p hp => graphCutRetract_tree p hp)
    | some a => exact continuous_const.continuousOn.congr (fun p hp => graphCutStub_retract hp)

lemma graphMidpoint_coord_le {V : Type u} {i j : V} (hne : i≠j) (k : V) :
    graphEdgePoint i j (1/2) k ≤ 1/2 := by
  simp only [graphEdgePoint_apply]
  split_ifs <;> subst_vars <;> first | contradiction | norm_num
lemma graph_dominant_mem_cut {V : Type u} {T : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization (⊤ : SimpleGraph V)) {i : V} (hi : 1/2<p i) :
    p∈graphCutRealization T := by
  refine ⟨hp,?_⟩
  intro j k hjk _ he
  have hh := graphMidpoint_coord_le hjk i
  rw [←he] at hh
  linarith
lemma graphEdgePoint_lerp_vertex {V : Type u} (i j : V) (t s : ℝ) :
    (1-s) • graphEdgePoint i j t+s • graphVertex i=graphEdgePoint i j ((1-s)*t) := by
  ext k
  simp only [graphEdgePoint,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring
lemma graphCut_lerp_mem {V : Type u} (T : SimpleGraph V) (p : GraphCutSpace T)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    (1-s) • p.val+s • graphCutRetract T p∈graphCutRealization T := by
  rcases graphCut_cover p with hp|⟨i,j,hp⟩
  · rw [graphCutRetract_tree p hp,←add_smul]
    simp
  · have hr := graphCutStub_retract hp
    obtain ⟨hne,hadj,t,ht,he⟩ := hp
    have htm : t<1/2 := lt_of_le_of_ne ht.2 (by
      intro h; exact p.property.2 i j hne hadj (he.symm.trans (by rw [h])))
    rw [hr,←he,graphEdgePoint_lerp_vertex]
    have hu0 : 0≤(1-s)*t := mul_nonneg (by linarith [hs.2]) ht.1
    have hu1 : (1-s)*t≤t := mul_le_of_le_one_left ht.1 (by linarith [hs.1])
    have hu : (1-s)*t<1/2 := lt_of_le_of_lt hu1 htm
    apply graph_dominant_mem_cut (graphEdgePoint_mem (Or.inr (show (⊤ : SimpleGraph V).Adj i j from hne)) ⟨hu0,by linarith⟩) (i := i)
    simp [graphEdgePoint_apply,hne]
    linarith

def graphCutRetraction {V : Type u} [Finite V] (T : SimpleGraph V) :
    C(GraphCutSpace T,GraphSpace T) where
  toFun p := ⟨graphCutRetract T p,graphCutRetract_mem T p⟩
  continuous_toFun := (continuous_graphCutRetract T).subtype_mk _
def graphCutInclusion {V : Type u} (T : SimpleGraph V) : C(GraphSpace T,GraphCutSpace T) where
  toFun p := ⟨p.val,graphRealization_subset_cut T p.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _
def graphCutHomotopy {V : Type u} [Finite V] (T : SimpleGraph V) :
    (ContinuousMap.id (GraphCutSpace T)).Homotopy
      ((graphCutInclusion T).comp (graphCutRetraction T)) where
  toFun sp := ⟨(1-sp.1.val) • sp.2.val+sp.1.val • graphCutRetract T sp.2,
    graphCut_lerp_mem T sp.2 sp.1.property⟩
  continuous_toFun := (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)).add
    ((continuous_subtype_val.comp continuous_fst).smul
      ((continuous_graphCutRetract T).comp continuous_snd))).subtype_mk _
  map_zero_left p := by apply Subtype.ext; simp
  map_one_left p := by apply Subtype.ext; simp [graphCutInclusion,graphCutRetraction]
/-- Removing the non-tree edge midpoints leaves a contractible graph (tree with half-open stubs). -/
theorem graphCut_contractible {V : Type u} [Fintype V] {T : SimpleGraph V} (hT : T.IsTree) :
    ContractibleSpace (GraphCutSpace T) := by
  let := graphTree_contractible hT
  have hn := ((id_nullhomotopic (GraphSpace T)).comp_left
    (graphCutRetraction T)).comp_right (graphCutInclusion T)
  obtain ⟨a,ha⟩ := hn
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨a,ContinuousMap.Homotopic.trans ⟨graphCutHomotopy T⟩ ?_⟩
  simpa only [ContinuousMap.id_comp] using ha
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v
namespace EuclideanFiveColor
/-- A compact connected fiber joins both designated boundary sets. -/
def FiberCrosses {X : Type u} {Y : Type v} [TopologicalSpace X]
    (f : X → Y) (A B : Set X) (b : Y) : Prop :=
  ∃K : Set X, IsCompact K ∧ IsConnected K ∧ K⊆f ⁻¹' {b} ∧
    (K∩A).Nonempty ∧ (K∩B).Nonempty
lemma fiberCrosses_symm {X : Type u} {Y : Type v} [TopologicalSpace X]
    {f : X → Y} {A B : Set X} {b : Y} (h : FiberCrosses f A B b) : FiberCrosses f B A b := by
  obtain ⟨K,hK,hC,hf,hA,hB⟩ := h
  exact ⟨K,hK,hC,hf,hB,hA⟩
lemma compact_fiber_partition {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T1Space Y]
    (f : C(X,Y)) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (b : Y)
    (hn : ¬FiberCrosses f A B b) :
    ∃K₀ K₁ : Set X, IsCompact K₀ ∧ IsCompact K₁ ∧ Disjoint K₀ K₁ ∧
      K₀∪K₁=f ⁻¹' {b} ∧ Disjoint K₀ B ∧ Disjoint K₁ A := by
  let F : Set X := f ⁻¹' {b}
  have hF : IsClosed F := isClosed_singleton.preimage f.continuous
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let I : Set F := Subtype.val ⁻¹' A
  let O : Set F := Subtype.val ⁻¹' B
  have hI : IsCompact I := (hA.preimage continuous_subtype_val).isCompact
  have hO : IsCompact O := (hB.preimage continuous_subtype_val).isCompact
  have hno : ∀x∈I,Disjoint (connectedComponent x) O := by
    intro x hx
    apply disjoint_left.mpr
    intro y hy hOy
    apply hn
    refine ⟨Subtype.val '' connectedComponent x,
      isClosed_connectedComponent.isCompact.image continuous_subtype_val,
      isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn,?_,?_,?_⟩
    · rintro z ⟨w,hw,rfl⟩; exact w.property
    · exact ⟨x.val,⟨⟨x,mem_connectedComponent,rfl⟩,hx⟩⟩
    · exact ⟨y.val,⟨⟨y,hy,rfl⟩,hOy⟩⟩
  obtain ⟨Z₀,Z₁,hZ₀,hZ₁,hd,hcov,hIZ,hOZ⟩ := compact_component_partition hI hO hno
  refine ⟨Subtype.val '' Z₀,Subtype.val '' Z₁,hZ₀.image continuous_subtype_val,
    hZ₁.image continuous_subtype_val,?_,?_,?_,?_⟩
  · apply disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ ⟨z,hz,he⟩
    have hh : z=y := Subtype.ext he
    subst z
    exact disjoint_left.mp hd hy hz
  · rw [←image_union,hcov]
    ext x
    constructor
    · rintro ⟨y,_,rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x,hx⟩,mem_univ _,rfl⟩
  · apply disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hz
    exact disjoint_left.mp hd hx (hOZ hz)
  · apply disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hz
    exact disjoint_left.mp hd (hIZ hz) hx

/-- All finitely many non-crossing bad fibers can simultaneously be separated,
 with the prescribed inner/outer closed sets on opposite sides. -/
theorem finite_fiber_separation {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T1Space Y]
    (f : C(X,Y)) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B)
    (S : Finset Y) (hn : ∀b∈S,¬FiberCrosses f A B b) :
    ∃C₀ C₁ : Set X, IsCompact C₀ ∧ IsCompact C₁ ∧ Disjoint C₀ C₁ ∧
      A⊆C₀ ∧ B⊆C₁ ∧ f ⁻¹' (↑S : Set Y)⊆C₀∪C₁ := by
  choose K₀ K₁ hK using (fun b : S => compact_fiber_partition f hA hB b.val (hn b.val b.property))
  let Z₀ : Set X := ⋃b : S,K₀ b
  let Z₁ : Set X := ⋃b : S,K₁ b
  have hz₀ : IsCompact Z₀ := isCompact_iUnion fun b => (hK b).1
  have hz₁ : IsCompact Z₁ := isCompact_iUnion fun b => (hK b).2.1
  have hsub₀ (b : S) : K₀ b⊆f ⁻¹' {b.val} := by
    rw [←(hK b).2.2.2.1]; exact subset_union_left
  have hsub₁ (b : S) : K₁ b⊆f ⁻¹' {b.val} := by
    rw [←(hK b).2.2.2.1]; exact subset_union_right
  have h01 : Disjoint Z₀ Z₁ := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    obtain ⟨c,hc⟩ := mem_iUnion.mp hy
    have he : b=c := Subtype.ext ((hsub₀ b hb).symm.trans (hsub₁ c hc))
    subst c
    exact disjoint_left.mp (hK b).2.2.1 hb hc
  have h0B : Disjoint Z₀ B := by
    apply disjoint_left.mpr
    intro x hx hB
    obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hK b).2.2.2.2.1 hb hB
  have h1A : Disjoint Z₁ A := by
    apply disjoint_left.mpr
    intro x hx hA
    obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hK b).2.2.2.2.2 hb hA
  refine ⟨A∪Z₀,B∪Z₁,hA.isCompact.union hz₀,hB.isCompact.union hz₁,?_,subset_union_left,subset_union_left,?_⟩
  · exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hd,h1A.symm⟩,
      disjoint_union_right.mpr ⟨h0B,h01⟩⟩
  · intro x hx
    let b : S := ⟨f x,hx⟩
    have hh : x∈K₀ b∪K₁ b := by rw [(hK b).2.2.2.1]; rfl
    rcases hh with hh|hh
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨b,hh⟩))
    · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨b,hh⟩))
end EuclideanFiveColor
end

end OAI
