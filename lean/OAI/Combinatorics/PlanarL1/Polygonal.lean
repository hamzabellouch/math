import OAI.Combinatorics.PlanarL1.Drawing

namespace OAI

section

namespace PlanarL1.Topology
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite segment chain, represented by its value at every integer;
only the first `length + 1` values are used. -/
structure SegmentChain (S : Set E) (x y : E) (length : ℕ) where
  vertex : ℕ → E
  start : vertex 0=x
  finish : vertex length=y
  segment_mem : ∀ i, i<length → segment ℝ (vertex i) (vertex (i+1)) ⊆ S

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

def nil (x : E) : SegmentChain S x x 0 where
  vertex _ := x
  start := rfl
  finish := rfl
  segment_mem i hi := False.elim (Nat.not_lt_zero i hi)

noncomputable def append {z : E} (h : segment ℝ y z ⊆ S) : SegmentChain S x z (n+1) where
  vertex k := if k≤n then P.vertex k else z
  start := by simpa using P.start
  finish := by simp
  segment_mem i hi := by
    by_cases hin : i<n
    · simpa [hin.le,show i+1≤n by omega] using P.segment_mem i hin
    · have hie : i=n := by omega
      subst i
      simpa [P.finish] using h

/-- Remove a closed loop in a segment chain. -/
noncomputable def eraseLoop (i j : ℕ) (hij : i<j) (hjn : j≤n)
    (heq : P.vertex i=P.vertex j) : SegmentChain S x y (n-j+i) where
  vertex k := if k≤ i then P.vertex k else P.vertex (k+j-i)
  start := by simpa using P.start
  finish := by
    rcases eq_or_lt_of_le hjn with rfl | hjn
    · simpa using heq.trans P.finish
    · have hle : ¬ n-j+i≤ i := by omega
      simp only [hle,ite_false]
      convert P.finish using 1
      all_goals congr 1; omega
  segment_mem k hk := by
    by_cases hki : k< i
    · simpa [hki.le,show k+1≤ i by omega] using P.segment_mem k (by omega)
    · by_cases hke : k=i
      · subst k
        simp only [le_refl,ite_true,show ¬ i+1≤ i by omega,ite_false]
        have he : i+1+j-i=j+1 := by omega
        rw [he,heq]
        exact P.segment_mem j (by omega)
      · have hgt : i<k := by omega
        simp only [show ¬ k≤ i by omega,show ¬ k+1≤ i by omega,ite_false]
        have he : k+1+j-i=(k+j-i)+1 := by omega
        rw [he]
        exact P.segment_mem (k+j-i) (by omega)

/-- Replace several successive edges by one segment already known to lie
in the permitted set. -/
noncomputable def shortcut (i j : ℕ) (hij : i<j) (hjn : j≤n)
    (hseg : segment ℝ (P.vertex i) (P.vertex j) ⊆ S) :
    SegmentChain S x y (n-j+i+1) where
  vertex k := if k≤ i then P.vertex k else P.vertex (k+j-i-1)
  start := by simpa using P.start
  finish := by
    simp only [show ¬ n-j+i+1≤ i by omega,ite_false]
    convert P.finish using 1
    all_goals congr 1; omega
  segment_mem k hk := by
    by_cases hki : k< i
    · simpa [hki.le,show k+1≤ i by omega] using P.segment_mem k (by omega)
    · by_cases hke : k=i
      · subst k
        simp only [le_refl,ite_true,show ¬ i+1≤ i by omega,ite_false]
        have he : i+1+j-i-1=j := by omega
        simpa [he] using hseg
      · have hgt : i<k := by omega
        simp only [show ¬ k≤ i by omega,show ¬ k+1≤ i by omega,ite_false]
        have he : k+1+j-i-1=(k+j-i-1)+1 := by omega
        rw [he]
        exact P.segment_mem (k+j-i-1) (by omega)

/-- Delete the part between two intersecting, nonadjacent segments. -/
noncomputable def shortcutAt (i j : ℕ) (hij : i<j) (hjn : j<n) (z : E)
    (hzi : z ∈ segment ℝ (P.vertex i) (P.vertex (i+1)))
    (hzj : z ∈ segment ℝ (P.vertex j) (P.vertex (j+1))) :
    SegmentChain S x y (n-j+i+1) where
  vertex k := if k≤ i then P.vertex k else if k=i+1 then z else P.vertex (k+j-i-1)
  start := by simpa using P.start
  finish := by
    simp only [show ¬ n-j+i+1≤ i by omega,ite_false,show n-j+i+1≠i+1 by omega]
    convert P.finish using 1
    all_goals congr 1; omega
  segment_mem k hk := by
    by_cases hki : k< i
    · simpa [hki.le,show k+1≤ i by omega] using P.segment_mem k (by omega)
    · by_cases hke : k=i
      · subst k
        simp only [le_refl,ite_true,show ¬ i+1≤ i by omega,ite_false]
        exact ((convex_segment (P.vertex i) (P.vertex (i+1))).segment_subset
          (left_mem_segment ℝ _ _) hzi).trans (P.segment_mem i (by omega))
      · by_cases hke : k=i+1
        · subst k
          simp only [show ¬ i+1≤ i by omega,show ¬ i+1+1≤ i by omega,ite_false,
            ite_true,show ¬ i+1+1=i+1 by omega]
          have he : i+1+1+j-i-1=j+1 := by omega
          simpa [he] using ((convex_segment (P.vertex j) (P.vertex (j+1))).segment_subset
            hzj (right_mem_segment ℝ _ _)).trans (P.segment_mem j hjn)
        · have hgt : i+1<k := by omega
          simp only [show ¬ k≤ i by omega,show ¬ k+1≤ i by omega,ite_false,
            show k≠i+1 by omega,show k+1≠i+1 by omega]
          have he : k+1+j-i-1=(k+j-i-1)+1 := by omega
          rw [he]
          exact P.segment_mem (k+j-i-1) (by omega)
end SegmentChain

lemma PolygonallyJoined.exists_segmentChain {S : Set E} {x y : E}
    (h : PolygonallyJoined S x y) : ∃ n, Nonempty (SegmentChain S x y n) := by
  induction h with
  | refl => exact ⟨0,⟨SegmentChain.nil _⟩⟩
  | @tail y z h hyz ih =>
    obtain ⟨n,⟨P⟩⟩ := ih
    exact ⟨n+1,⟨P.append hyz⟩⟩

/-- A collinear broken segment covers the direct segment. -/
lemma collinear_segment_union {a b c : E} (h : Collinear ℝ ({a,b,c} : Set E)) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  by_cases hac : a=c
  · subst c
    simp only [segment_same,singleton_subset_iff,mem_union]
    exact Or.inl (left_mem_segment ℝ a b)
  have hb : b ∈ line[ℝ,a,c] := h.mem_affineSpan_of_mem_of_ne
    (by simp) (by simp) (by simp) hac
  obtain ⟨t,ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hb
  apply (openSegment_subset_iff_segment_subset (𝕜 := ℝ)
    (s := segment ℝ a b ∪ segment ℝ b c)
    (Or.inl (left_mem_segment ℝ a b)) (Or.inr (right_mem_segment ℝ b c))).mp
  intro z hz
  rcases openSegment_subset_union a c (⟨t,ht⟩ : b ∈ Set.range (AffineMap.lineMap a c : ℝ → E)) hz with
    hzb | hzb | hzb
  · exact Or.inl (hzb ▸ right_mem_segment ℝ a b)
  · exact Or.inl (openSegment_subset_segment ℝ a b hzb)
  · exact Or.inr (openSegment_subset_segment ℝ b c hzb)

/-- Adjacent non-collinear segments have no intersection except their common
endpoint. This elementary fact supplies loop erasure without a Jordan theorem. -/
lemma collinear_of_adjacent_overlap {a b c z : E}
    (hz : z ∈ segment ℝ a b) (hz' : z ∈ segment ℝ b c) (hne : z≠b) :
    Collinear ℝ ({a,b,c} : Set E) := by
  have h₁ := (mem_segment_iff_wbtw.mp hz).collinear
  have h₂ := (mem_segment_iff_wbtw.mp hz').collinear
  have h₂' : Collinear ℝ ({c,b,z} : Set E) := by
    have hs : ({c,b,z} : Set E) = {b,z,c} := by
      ext w
      simp only [mem_insert_iff,mem_singleton_iff]
      tauto
    rw [hs]
    exact h₂
  have hh := (h₁.collinear_insert_iff_of_ne (p₁:=c) (p₂:=b) (p₃:=z)
    (by simp) (by simp) hne.symm).mpr h₂'
  exact Collinear.subset (by
    intro w hw
    simp only [mem_insert_iff,mem_singleton_iff] at hw ⊢
    tauto) hh

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

def IsMinimal (_P : SegmentChain S x y n) : Prop :=
  ∀ m, Nonempty (SegmentChain S x y m) → n ≤ m

def IsSimple : Prop :=
  Set.InjOn P.vertex (Set.Iic n) ∧
    ∀ i j, i<j → j<n → ∀ z,
      z ∈ segment ℝ (P.vertex i) (P.vertex (i+1)) →
      z ∈ segment ℝ (P.vertex j) (P.vertex (j+1)) →
      j=i+1 ∧ z=P.vertex j

lemma minimal_vertex_injective (h : P.IsMinimal) : Set.InjOn P.vertex (Set.Iic n) := by
  intro i hi j hj heq
  change i ≤ n at hi
  change j ≤ n at hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hh := h (n-j+i) ⟨P.eraseLoop i j hij hj heq⟩
    omega
  · have hh := h (n-i+j) ⟨P.eraseLoop j i hji hi heq.symm⟩
    omega

lemma minimal_nonadjacent (h : P.IsMinimal) {i j : ℕ} (hij : i+1<j) (hjn : j<n) :
    Disjoint (segment ℝ (P.vertex i) (P.vertex (i+1)))
      (segment ℝ (P.vertex j) (P.vertex (j+1))) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hh := h (n-j+i+1) ⟨P.shortcutAt i j (by omega) hjn z hzi hzj⟩
  omega

lemma minimal_adjacent (h : P.IsMinimal) {i : ℕ} (hi : i+1<n) {z : E}
    (hzi : z ∈ segment ℝ (P.vertex i) (P.vertex (i+1)))
    (hzj : z ∈ segment ℝ (P.vertex (i+1)) (P.vertex (i+1+1))) : z=P.vertex (i+1) := by
  by_contra hne
  have hcol := collinear_of_adjacent_overlap hzi hzj hne
  have hseg : segment ℝ (P.vertex i) (P.vertex (i+1+1)) ⊆ S :=
    (collinear_segment_union hcol).trans (Set.union_subset (P.segment_mem i (by omega))
      (P.segment_mem (i+1) hi))
  have hh := h (n-(i+1+1)+i+1) ⟨P.shortcut i (i+1+1) (by omega) (by omega) hseg⟩
  omega

lemma minimal_simple (h : P.IsMinimal) : P.IsSimple := by
  refine ⟨P.minimal_vertex_injective h,fun i j hij hjn z hzi hzj => ?_⟩
  by_cases heq : j=i+1
  · subst j
    exact ⟨rfl,P.minimal_adjacent h hjn hzi hzj⟩
  · exact False.elim (Set.disjoint_left.mp (P.minimal_nonadjacent h (by omega) hjn) hzi hzj)
end SegmentChain

/-- Every finite polygonal connection contains a simple finite polygonal
connection with the same endpoints and no larger trace. -/
lemma PolygonallyJoined.exists_simple_segmentChain {S : Set E} {x y : E}
    (h : PolygonallyJoined S x y) :
    ∃ n, ∃ P : SegmentChain S x y n, P.IsSimple := by
  classical
  let hh := h.exists_segmentChain
  let n := Nat.find hh
  let P := Classical.choice (Nat.find_spec hh)
  exact ⟨n,P,P.minimal_simple (fun m hm => Nat.find_min' hh hm)⟩

end PlanarL1.Topology

namespace PlanarL1.Topology
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma PolygonallyJoined.mono {S T : Set E} {x y : E}
    (h : PolygonallyJoined S x y) (hST : S ⊆ T) : PolygonallyJoined T x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hab ih => exact ih.tail (hab.trans hST)

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

/-- The finite geometric trace, including the degenerate chain's endpoint. -/
def trace : Set E := {x} ∪ ⋃ i : Fin n, segment ℝ (P.vertex i) (P.vertex (i+1))

lemma trace_subset (hx : x ∈ S) : P.trace ⊆ S := by
  rintro z (rfl | hz)
  · exact hx
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact P.segment_mem i i.isLt hi

lemma vertex_mem_trace (i : ℕ) (hi : i ≤ n) : P.vertex i ∈ P.trace := by
  by_cases h0 : i=0
  · simp [h0,P.start,trace]
  · have hi' : i-1<n := by omega
    exact Or.inr (mem_iUnion.mpr ⟨⟨i-1,hi'⟩,by
      have he : i-1+1=i := by omega
      simpa only [he] using right_mem_segment ℝ (P.vertex (i-1)) (P.vertex i)⟩)

lemma start_mem_trace : x ∈ P.trace := Or.inl rfl
lemma finish_mem_trace : y ∈ P.trace := by
  have h := P.vertex_mem_trace n le_rfl
  rwa [P.finish] at h

end SegmentChain

lemma radial_segment_dist_le {x y z : E} {r : ℝ} (hr : 0 ≤ r) (hy : dist y x=r)
    (hz : z ∈ segment ℝ x y) : dist z x ≤ r := by
  exact (convex_closedBall x r).segment_subset (by simpa using hr)
    (by simp [Metric.mem_closedBall,hy] : y ∈ closedBall x r) hz

namespace Drawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)
variable {r : ℝ} (T : ∀ d : ForwardDart G, D.EdgeTrim r d.val)

/-- A boundary port and its incident vertex. -/
def portVertex (d : ForwardDart G) (b : Bool) : V := if b then d.val.snd else d.val.fst
noncomputable def port (d : ForwardDart G) (b : Bool) : ℂ :=
  D.edge d.val.fst d.val.snd d.val.adj (if b then (T d).last else (T d).first)
noncomputable def head (d : ForwardDart G) (b : Bool) : Set ℂ :=
  segment ℝ (D.point (portVertex d b)) (D.port T d b)

lemma port_sphere (d : ForwardDart G) (b : Bool) :
    dist (D.port T d b) (D.point (portVertex d b))=r := by
  cases b
  · exact (T d).first_sphere
  · exact (T d).last_sphere

lemma head_dist {d : ForwardDart G} {b : Bool} {z : ℂ} (hr : 0<r)
    (hz : z ∈ D.head T d b) : dist z (D.point (portVertex d b)) ≤ r :=
  radial_segment_dist_le hr.le (D.port_sphere T d b) hz

lemma ports_distinct {d e : ForwardDart G} (hde : d≠e) (b c : Bool) :
    D.port T d b ≠ D.port T e c := by
  intro he
  have h (d : ForwardDart G) (b : Bool) :
      0<((if b then (T d).last else (T d).first : unitInterval):ℝ) ∧
      ((if b then (T d).last else (T d).first : unitInterval):ℝ)<1 := by
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact ⟨(T d).first_pos,by linarith [(T d).first_lt]⟩
    · exact ⟨by linarith [(T d).last_gt],(T d).last_lt_one⟩
  exact hde (ForwardDart.eq_of_endpoints d e (D.interior_disjoint _ _ _ _ _ _ _ _
    (h d b).1 (h d b).2 (h e c).1 (h e c).2 he))

lemma heads_intersect (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    {d e : ForwardDart G} (hde : d≠e) {b c : Bool} {z : ℂ}
    (hz : z ∈ D.head T d b) (hz' : z ∈ D.head T e c) :
    z=D.point (portVertex d b) ∧ z=D.point (portVertex e c) := by
  have heq : portVertex d b=portVertex e c := by
    by_contra hne
    have hfar := hsep (portVertex d b) (D.point (portVertex e c))
      (D.point_mem_forbidden _ _ (fun h => hne h.symm))
    have ht := dist_triangle (D.point (portVertex d b)) z (D.point (portVertex e c))
    have h₁ := D.head_dist T hr hz
    have h₂ := D.head_dist T hr hz'
    rw [dist_comm z (D.point (portVertex d b))] at h₁
    linarith
  have hw : dist (D.port T e c) (D.point (portVertex d b))=r :=
    heq ▸ D.port_sphere T e c
  have he : z=D.point (portVertex d b) := radial_heads_intersect hr
    (D.port_sphere T d b) hw (D.ports_distinct T hde b c) hz (by simpa [head,heq] using hz')
  exact ⟨he,he.trans (congrArg D.point heq)⟩

lemma vertex_mem_head (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    {d : ForwardDart G} {b : Bool} {w : V} (hw : D.point w ∈ D.head T d b) :
    w=portVertex d b := by
  by_contra hne
  have hfar := hsep (portVertex d b) (D.point w) (D.point_mem_forbidden _ _ hne)
  have hn := D.head_dist T hr hw
  rw [dist_comm] at hn
  linarith

lemma head_mem_obstacle {d e : ForwardDart G} (hde : e≠d) (b : Bool) :
    D.head T e b ⊆ D.middleObstacle T d := by
  intro z hz
  apply Or.inr
  refine mem_iUnion.mpr ⟨⟨e,hde⟩,?_⟩
  cases b
  · exact Or.inl hz
  · exact Or.inr hz

noncomputable def edgeRegion (U : ForwardDart G → Set ℂ) (d : ForwardDart G) : Set ℂ :=
  U d ∪ (D.head T d false ∪ D.head T d true)

lemma region_joined {U : ForwardDart G → Set ℂ} (d : ForwardDart G)
    (h : PolygonallyJoined (U d) (D.port T d false) (D.port T d true)) :
    PolygonallyJoined (D.edgeRegion T U d) (D.point d.val.fst) (D.point d.val.snd) := by
  have h₁ : PolygonallyJoined (D.edgeRegion T U d) (D.point d.val.fst) (D.port T d false) :=
    Relation.ReflTransGen.single (fun _ hz => Or.inr (Or.inl hz))
  have h₂ : PolygonallyJoined (D.edgeRegion T U d) (D.port T d true) (D.point d.val.snd) :=
    Relation.ReflTransGen.single (fun _ hz => Or.inr (Or.inr (by
      simpa [head,portVertex,segment_symm] using hz)))
  exact (h₁.trans (h.mono Set.subset_union_left)).trans h₂

lemma region_vertex (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    {U : ForwardDart G → Set ℂ} (hU : ∀ d, Disjoint (U d) (D.middleObstacle T d))
    {d : ForwardDart G} {w : V} (hw : D.point w ∈ D.edgeRegion T U d) :
    w=d.val.fst ∨ w=d.val.snd := by
  rcases hw with hw | hw | hw
  · exact False.elim (Set.disjoint_left.mp (hU d) hw (Or.inl ⟨w,rfl⟩))
  · exact Or.inl (D.vertex_mem_head T hr hsep hw)
  · exact Or.inr (D.vertex_mem_head T hr hsep hw)

lemma regions_intersect (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    {U : ForwardDart G → Set ℂ} (hU : ∀ d, Disjoint (U d) (D.middleObstacle T d))
    (hUU : Pairwise (fun d e => Disjoint (U d) (U e)))
    {d e : ForwardDart G} (hde : d≠e) {z : ℂ}
    (hz : z ∈ D.edgeRegion T U d) (hz' : z ∈ D.edgeRegion T U e) :
    (z=D.point d.val.fst ∨ z=D.point d.val.snd) ∧
      (z=D.point e.val.fst ∨ z=D.point e.val.snd) := by
  have leftHead (b : Bool) (hb : z ∈ D.head T d b) : z ∉ U e := by
    intro hu
    exact Set.disjoint_left.mp (hU e) hu (D.head_mem_obstacle T hde b hb)
  have rightHead (b : Bool) (hb : z ∈ D.head T e b) : z ∉ U d := by
    intro hu
    exact Set.disjoint_left.mp (hU d) hu (D.head_mem_obstacle T hde.symm b hb)
  rcases hz with hz | hz | hz <;> rcases hz' with hz' | hz' | hz'
  · exact False.elim (Set.disjoint_left.mp (hUU hde) hz hz')
  · exact False.elim (rightHead false hz' hz)
  · exact False.elim (rightHead true hz' hz)
  · exact False.elim (leftHead false hz hz')
  · have he := D.heads_intersect T hr hsep hde hz hz'
    exact ⟨Or.inl he.1,Or.inl he.2⟩
  · have he := D.heads_intersect T hr hsep hde hz hz'
    exact ⟨Or.inl he.1,Or.inr he.2⟩
  · exact False.elim (leftHead true hz hz')
  · have he := D.heads_intersect T hr hsep hde hz hz'
    exact ⟨Or.inr he.1,Or.inl he.2⟩
  · have he := D.heads_intersect T hr hsep hde hz hz'
    exact ⟨Or.inr he.1,Or.inr he.2⟩

end Drawing
end PlanarL1.Topology

namespace PlanarL1.Topology
open Set

namespace SegmentChain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S T : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

def mapSet (h : S ⊆ T) : SegmentChain T x y n where
  vertex := P.vertex
  start := P.start
  finish := P.finish
  segment_mem i hi := (P.segment_mem i hi).trans h

lemma mapSet_simple (h : S ⊆ T) (hP : P.IsSimple) : (P.mapSet h).IsSimple := hP
lemma mapSet_trace (h : S ⊆ T) : (P.mapSet h).trace=P.trace := rfl

end SegmentChain

/-- A literal finite polyline drawing. Simplicity is a proved property of the
finite segment chains, not an added planarity promise. -/
structure PLDrawing {V : Type} [LinearOrder V] (G : SimpleGraph V) where
  point : V → ℂ
  point_injective : Function.Injective point
  count : ForwardDart G → ℕ
  chain : ∀ d : ForwardDart G, SegmentChain Set.univ (point d.val.fst) (point d.val.snd) (count d)
  simple : ∀ d, (chain d).IsSimple
  on_vertex : ∀ d w, point w ∈ (chain d).trace → w=d.val.fst ∨ w=d.val.snd
  intersect : ∀ d e, d≠e → ∀ z, z ∈ (chain d).trace → z ∈ (chain e).trace →
    (z=point d.val.fst ∨ z=point d.val.snd) ∧ (z=point e.val.fst ∨ z=point e.val.snd)

/-- Simultaneous polygonalization of a finite topological graph drawing.
The original positions of all vertices are retained. -/
lemma Drawing.polygonal {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V}
    (D : Drawing G) : ∃ P : PLDrawing G, P.point=D.point := by
  classical
  obtain ⟨r,hr,hsep⟩ := D.uniform_vertex_disks
  let T (d : ForwardDart G) : D.EdgeTrim r d.val :=
    Classical.choice (D.edgeTrim_nonempty hr hsep d.val)
  obtain ⟨U,hU,hUU⟩ := D.polygonal_middles T hr hsep
  have hj (d : ForwardDart G) := D.region_joined T d (hU d).2.2
  choose n P hP using fun d => (hj d).exists_simple_segmentChain
  have hstart (d : ForwardDart G) : D.point d.val.fst ∈ D.edgeRegion T U d :=
    Or.inr (Or.inl (left_mem_segment ℝ _ _))
  refine ⟨⟨D.point,D.point_injective,n,fun d => (P d).mapSet (Set.subset_univ _),
    fun d => (P d).mapSet_simple _ (hP d),?_,?_⟩,rfl⟩
  · intro d w hw
    apply D.region_vertex T hr hsep (fun d => (hU d).2.1)
    exact (P d).trace_subset (hstart d) hw
  · intro d e hde z hz hz'
    exact D.regions_intersect T hr hsep (fun d => (hU d).2.1) hUU hde
      ((P d).trace_subset (hstart d) hz) ((P e).trace_subset (hstart e) hz')

lemma polygonal_of_planar {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V}
    (h : IsPlanar G) : Nonempty (PLDrawing G) := by
  obtain ⟨D⟩ := drawing_of_planar h
  obtain ⟨P,_⟩ := D.polygonal
  exact ⟨P⟩

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Boundary points of a convex neighbourhood have a unique positive radial
coordinate. This will keep the extended leaf ports disjoint when shrinking
an embedded finite tree inside a convex merging region. -/
lemma convex_frontier_radial_injective {S : Set E} (hS : Convex ℝ S)
    (h0 : S ∈ nhds (0:E)) {p q : E} (hp : p ∈ frontier S) (hq : q ∈ frontier S)
    {s t : ℝ} (hs : 0<s) (ht : 0<t) (he : s • p=t • q) : s=t ∧ p=q := by
  have hp' : gauge S p=1 := (gauge_eq_one_iff_mem_frontier hS h0).mpr hp
  have hq' : gauge S q=1 := (gauge_eq_one_iff_mem_frontier hS h0).mpr hq
  have h := congrArg (gauge S) he
  rw [gauge_smul_of_nonneg hs.le, gauge_smul_of_nonneg ht.le, hp',hq'] at h
  simp only [smul_eq_mul,mul_one] at h
  refine ⟨h,?_⟩
  subst t
  exact smul_right_injective E hs.ne' he

/-- The outer radial tails from different ports never meet, including their
endpoints. -/
lemma convex_frontier_tails_disjoint {S : Set E} (hS : Convex ℝ S)
    (h0 : S ∈ nhds (0:E)) {p q : E} (hp : p ∈ frontier S) (hq : q ∈ frontier S)
    (hpq : p≠q) {c : ℝ} (hc : 0<c) (hc1 : c≤1) :
    Disjoint (segment ℝ (c•p) p) (segment ℝ (c•q) q) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rw [segment_eq_image' ℝ (c•p) p] at hz
  rw [segment_eq_image' ℝ (c•q) q] at hz'
  obtain ⟨s,hs,rfl⟩ := hz
  obtain ⟨t,ht,he⟩ := hz'
  have hform (u : ℝ) (v : E) : c•v+u•(v-c•v)=(c+u*(1-c))•v := by
    module
  dsimp only at he
  rw [hform,hform] at he
  have hs' : 0<c+s*(1-c) := by nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hc1)]
  have ht' : 0<c+t*(1-c) := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hc1)]
  exact hpq (convex_frontier_radial_injective hS h0 hp hq hs' ht' he.symm).2

lemma convex_frontier_tail_core {S : Set E} (hS : Convex ℝ S)
    (h0 : S ∈ nhds (0:E)) {p z : E} (hp : p ∈ frontier S)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hz : z ∈ segment ℝ (c•p) p) (hcore : z ∈ (fun x : E => c•x) '' closure S) : z=c•p := by
  rw [segment_eq_image' ℝ (c•p) p] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  obtain ⟨w,hw,he⟩ := hcore
  have hform : c•p+t•(p-c•p)=(c+t*(1-c))•p := by module
  dsimp only at he ⊢
  rw [hform] at he ⊢
  have hg := congrArg (gauge S) he
  have hp' := (gauge_eq_one_iff_mem_frontier hS h0).mpr hp
  have hcoef : 0≤c+t*(1-c) := add_nonneg hc.le (mul_nonneg ht.1 (sub_nonneg.mpr hc1))
  rw [gauge_smul_of_nonneg hc.le,gauge_smul_of_nonneg hcoef,hp',smul_eq_mul,smul_eq_mul,mul_one] at hg
  have hw' : gauge S w≤1 := (gauge_le_one_iff_mem_closure hS h0).mpr hw
  have hle : c+t*(1-c)≤c := by nlinarith
  have hge : c≤c+t*(1-c) := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hc1)]
  rw [le_antisymm hle hge]

end PlanarL1.Topology

namespace PlanarL1.Topology
open Set Metric Filter

/-- A straight selected tree piece has an arbitrarily thin bounded convex
merging region avoiding every closed nonincident obstacle. -/
lemma convex_tube_avoiding {a b : ℂ} {F : Set ℂ} (hF : IsClosed F)
    (hdisj : Disjoint (segment ℝ a b) F) :
    ∃ S : Set ℂ, Convex ℝ S ∧ IsOpen S ∧ Bornology.IsBounded S ∧
      segment ℝ a b ⊆ S ∧ Disjoint (closure S) F := by
  obtain ⟨r,hr,hsub⟩ := (compact_segment_complex a b).exists_cthickening_subset_open
    hF.isOpen_compl hdisj.subset_compl_right
  refine ⟨thickening r (segment ℝ a b),(convex_segment a b).thickening r,
    isOpen_thickening,?_,self_subset_thickening hr _,?_⟩
  · exact (compact_segment_complex a b).isBounded.thickening
  · exact Set.disjoint_left.mpr (fun z hz hzF =>
      hsub (closure_thickening_subset_cthickening r _ hz) hzF)

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma image_segment_smul (c : ℝ) (x y : E) :
    (fun z : E => c•z) '' segment ℝ x y=segment ℝ (c•x) (c•y) := by
  simp only [segment_eq_image' ℝ,Set.image_image]
  congr 1
  funext t
  module

lemma PolygonallyJoined.smul {S : Set E} {x y : E}
    (h : PolygonallyJoined S x y) (c : ℝ) :
    PolygonallyJoined ((fun z : E => c•z) '' S) (c•x) (c•y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hab ih =>
    refine ih.tail ?_
    rw [← image_segment_smul]
    exact Set.image_mono hab

lemma SegmentChain.joined_trace {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n) :
    PolygonallyJoined P.trace x y := by
  have h : ∀ i, i≤n → PolygonallyJoined P.trace x (P.vertex i) := by
    intro i
    induction i with
    | zero => intro _; rw [P.start]; exact Relation.ReflTransGen.refl
    | succ i ih =>
      intro hi
      refine (ih (by omega)).tail ?_
      intro z hz
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i,by omega⟩,hz⟩)
  simpa only [P.finish] using h n le_rfl

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

def Incident (d : ForwardDart G) (v : V) : Prop := v=d.val.fst ∨ v=d.val.snd

lemma leaf_incident_unique {B : Set V}
    (hleaf : ∀ v ∈ B, ∀ a b, G.Adj v a → G.Adj v b → a=b)
    {v : V} (hv : v∈B) {d e : ForwardDart G}
    (hd : Incident d v) (he : Incident e v) : d=e := by
  rcases hd with hd | hd <;> rcases he with he | he
  · have hv' : d.val.fst=e.val.fst := hd.symm.trans he
    apply ForwardDart.eq_of_endpoints
    exact Or.inl ⟨hv',hleaf v hv _ _ (hd.symm ▸ d.val.adj) (he.symm ▸ e.val.adj)⟩
  · have hv' : d.val.fst=e.val.snd := hd.symm.trans he
    apply ForwardDart.eq_of_endpoints
    exact Or.inr ⟨hv',hleaf v hv _ _ (hd.symm ▸ d.val.adj) (he.symm ▸ e.val.adj.symm)⟩
  · have hv' : d.val.snd=e.val.fst := hd.symm.trans he
    apply ForwardDart.eq_of_endpoints
    exact Or.inr ⟨hleaf v hv _ _ (hd.symm ▸ d.val.adj.symm) (he.symm ▸ e.val.adj),hv'⟩
  · have hv' : d.val.snd=e.val.snd := hd.symm.trans he
    apply ForwardDart.eq_of_endpoints
    exact Or.inl ⟨hleaf v hv _ _ (hd.symm ▸ d.val.adj.symm) (he.symm ▸ e.val.adj.symm),hv'⟩

noncomputable def expandedPoint (B : Set V) (c : ℝ) (v : V) : ℂ :=
  by classical exact if v∈B then P.point v else c•P.point v

def portTail (c : ℝ) (v : V) : Set ℂ := segment ℝ (c•P.point v) (P.point v)

def expandedRegion (B : Set V) (c : ℝ) (d : ForwardDart G) : Set ℂ :=
  (fun z : ℂ => c•z) '' (P.chain d).trace ∪
    ⋃ v : {v : V // v∈B ∧ Incident d v}, P.portTail c v.val

variable {S : Set ℂ} (hS : Convex ℝ S) (h0 : S ∈ nhds (0:ℂ))
  (hpoint : ∀ v, P.point v ∈ closure S)
  {B : Set V} (hport : ∀ v ∈ B, P.point v ∈ frontier S)
  {c : ℝ} (hc : 0<c) (hc1 : c<1)

include hS h0 hport hc hc1

lemma port_not_core {v : V} (hv : v∈B) :
    P.point v ∉ (fun z : ℂ => c•z) '' closure S := by
  rintro ⟨z,hz,he⟩
  have hg := congrArg (gauge S) he
  rw [gauge_smul_of_nonneg hc.le,
    (gauge_eq_one_iff_mem_frontier hS h0).mpr (hport v hv)] at hg
  have hz' := (gauge_le_one_iff_mem_closure hS h0).mpr hz
  change c*gauge S z=1 at hg
  nlinarith

include hpoint

lemma expandedPoint_injective : Function.Injective (P.expandedPoint B c) := by
  classical
  intro v w he
  by_cases hv : v∈B <;> by_cases hw : w∈B
  · exact P.point_injective (by simpa [expandedPoint,hv,hw] using he)
  · exfalso
    apply P.port_not_core hS h0 hport hc hc1 hv
    exact ⟨P.point w,hpoint w,by simpa [expandedPoint,hv,hw] using he.symm⟩
  · exfalso
    apply P.port_not_core hS h0 hport hc hc1 hw
    exact ⟨P.point v,hpoint v,by simpa [expandedPoint,hv,hw] using he⟩
  · apply P.point_injective
    exact smul_right_injective ℂ hc.ne' (by simpa [expandedPoint,hv,hw] using he)

lemma newpoint_in_tail {v w : V} (hw : w∈B)
    (hv : P.expandedPoint B c v ∈ P.portTail c w) : v=w := by
  classical
  by_cases hvB : v∈B
  · by_contra hne
    have hd := convex_frontier_tails_disjoint hS h0 (hport v hvB) (hport w hw)
      (fun h => hne (P.point_injective h)) hc hc1.le
    exact Set.disjoint_left.mp hd (right_mem_segment ℝ _ _)
      (by simpa [expandedPoint,hvB,portTail] using hv)
  · apply P.point_injective
    apply smul_right_injective ℂ hc.ne'
    exact convex_frontier_tail_core hS h0 (hport w hw) hc hc1.le
      (by simpa [expandedPoint,hvB,portTail] using hv) ⟨P.point v,hpoint v,rfl⟩

omit hpoint in
lemma newpoint_in_core {d : ForwardDart G} {v : V}
    (hv : P.expandedPoint B c v ∈ (fun z : ℂ => c•z) '' (P.chain d).trace)
    (htrace : (P.chain d).trace ⊆ closure S) : ¬v∈B ∧ Incident d v := by
  classical
  have hvB : ¬v∈B := by
    intro h
    apply P.port_not_core hS h0 hport hc hc1 h
    simpa [expandedPoint,h] using Set.image_mono htrace hv
  refine ⟨hvB,?_⟩
  obtain ⟨z,hz,he⟩ := hv
  have he' : z=P.point v := smul_right_injective ℂ hc.ne'
    (by simpa [expandedPoint,hvB] using he)
  exact P.on_vertex d v (he' ▸ hz)

lemma expandedRegion_vertex {d : ForwardDart G} {v : V}
    (htrace : (P.chain d).trace ⊆ closure S)
    (hv : P.expandedPoint B c v ∈ P.expandedRegion B c d) : Incident d v := by
  rcases hv with hv | hv
  · exact (P.newpoint_in_core hS h0 hport hc hc1 hv htrace).2
  · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hv
    have he := P.newpoint_in_tail hS h0 hpoint hport hc hc1 w.property.1 hw
    exact he ▸ w.property.2


variable (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
  (hleaf : ∀ v ∈ B, ∀ a b, G.Adj v a → G.Adj v b → a=b)
include htrace hleaf

omit hpoint in
lemma different_core_tail {d e : ForwardDart G} (hde : d≠e)
    {v : V} (hv : v∈B) (he : Incident e v) :
    Disjoint ((fun z : ℂ => c•z) '' (P.chain d).trace) (P.portTail c v) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨w,hw,rfl⟩ := hz
  have heq := convex_frontier_tail_core hS h0 (hport v hv) hc hc1.le hz'
    ⟨w,htrace d hw,rfl⟩
  have hwv : w=P.point v := smul_right_injective ℂ hc.ne' heq
  have hd : Incident d v := P.on_vertex d v (hwv ▸ hw)
  exact hde (leaf_incident_unique hleaf hv hd he)

omit hpoint htrace in
lemma different_tails {d e : ForwardDart G} (hde : d≠e)
    {v w : V} (hv : v∈B) (hw : w∈B) (hd : Incident d v) (he : Incident e w) :
    Disjoint (P.portTail c v) (P.portTail c w) := by
  apply convex_frontier_tails_disjoint hS h0 (hport v hv) (hport w hw) _ hc hc1.le
  intro h
  have hvw := P.point_injective h
  exact hde (leaf_incident_unique hleaf hv hd (hvw.symm ▸ he))

omit hpoint in
lemma expandedRegions_intersect {d e : ForwardDart G} (hde : d≠e)
    {z : ℂ} (hz : z∈P.expandedRegion B c d) (hz' : z∈P.expandedRegion B c e) :
    (z=P.expandedPoint B c d.val.fst ∨ z=P.expandedPoint B c d.val.snd) ∧
    (z=P.expandedPoint B c e.val.fst ∨ z=P.expandedPoint B c e.val.snd) := by
  classical
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · obtain ⟨w,hw,rfl⟩ := hz
    obtain ⟨w',hw',heq⟩ := hz'
    have heww : w'=w := smul_right_injective ℂ hc.ne' heq
    subst w'
    have hint := P.intersect d e hde w hw hw'
    have hnB (v : V) (h : w=P.point v) : v∉B := by
      intro hv
      exact hde (leaf_incident_unique hleaf hv (P.on_vertex d v (h ▸ hw))
        (P.on_vertex e v (h ▸ hw')))
    constructor
    · rcases hint.1 with hd | hd
      · exact Or.inl (by simp [expandedPoint,hnB _ hd,hd])
      · exact Or.inr (by simp [expandedPoint,hnB _ hd,hd])
    · rcases hint.2 with he | he
      · exact Or.inl (by simp [expandedPoint,hnB _ he,he])
      · exact Or.inr (by simp [expandedPoint,hnB _ he,he])
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz'
    exact False.elim (Set.disjoint_left.mp
      (P.different_core_tail hS h0 hport hc hc1 htrace hleaf hde v.property.1 v.property.2) hz hv)
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    exact False.elim (Set.disjoint_left.mp
      (P.different_core_tail hS h0 hport hc hc1 htrace hleaf hde.symm v.property.1 v.property.2) hz' hv)
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hz'
    exact False.elim (Set.disjoint_left.mp
      (P.different_tails hS h0 hport hc hc1 hleaf hde
        v.property.1 w.property.1 v.property.2 w.property.2) hv hw)

omit hS h0 hport hc hc1 hpoint htrace hleaf in
lemma expandedPoint_mem_region {B : Set V} {c : ℝ} {d : ForwardDart G} {v : V}
    (hv : Incident d v) : P.expandedPoint B c v ∈ P.expandedRegion B c d := by
  classical
  by_cases hvB : v∈B
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨v,hvB,hv⟩,by
      simpa [expandedPoint,hvB,portTail] using right_mem_segment ℝ (c•P.point v) (P.point v)⟩)
  · apply Or.inl
    refine ⟨P.point v,?_,by simp [expandedPoint,hvB]⟩
    rcases hv with rfl | rfl
    · exact (P.chain d).start_mem_trace
    · exact (P.chain d).finish_mem_trace

omit hS h0 hport hc hc1 hpoint htrace hleaf in
lemma expandedRegion_joined (B : Set V) (c : ℝ) (d : ForwardDart G) :
    PolygonallyJoined (P.expandedRegion B c d)
      (P.expandedPoint B c d.val.fst) (P.expandedPoint B c d.val.snd) := by
  classical
  have hseg (v : V) (hv : Incident d v) :
      segment ℝ (c•P.point v) (P.expandedPoint B c v) ⊆ P.expandedRegion B c d := by
    by_cases hvB : v∈B
    · intro z hz
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨v,hvB,hv⟩,
        by simpa [expandedPoint,hvB,portTail] using hz⟩)
    · simp only [expandedPoint,hvB,ite_false,segment_same]
      intro z hz
      have he : z=c•P.point v := hz
      subst z
      simpa [expandedPoint,hvB] using P.expandedPoint_mem_region (B:=B) (c:=c) hv
  have hfirst : PolygonallyJoined (P.expandedRegion B c d)
      (P.expandedPoint B c d.val.fst) (c•P.point d.val.fst) :=
    Relation.ReflTransGen.single (by rw [segment_symm]; exact hseg _ (Or.inl rfl))
  have hmiddle := ((P.chain d).joined_trace.smul c).mono
    (show (fun z : ℂ => c•z) '' (P.chain d).trace ⊆ P.expandedRegion B c d from fun _ h => Or.inl h)
  exact (hfirst.trans hmiddle).tail (hseg _ (Or.inr rfl))

/-- Inside a convex merging region, shrink the complete drawn core but retain
all its distinct leaf ports. Extending each leaf radially introduces no
intersections. The result is again an actual finite polyline drawing. -/
lemma expand_leaf_ports : ∃ Q : PLDrawing G,
    Q.point=P.expandedPoint B c ∧ ∀ d, (Q.chain d).trace ⊆ P.expandedRegion B c d := by
  classical
  choose n R hR using fun d => (P.expandedRegion_joined B c d).exists_simple_segmentChain
  have hstart (d : ForwardDart G) := P.expandedPoint_mem_region (B:=B) (c:=c) (d:=d) (Or.inl rfl)
  refine ⟨⟨P.expandedPoint B c,P.expandedPoint_injective hS h0 hpoint hport hc hc1,
    n,fun d => (R d).mapSet (Set.subset_univ _),
    fun d => (R d).mapSet_simple _ (hR d),?_,?_⟩,rfl,?_⟩
  · intro d v hv
    exact P.expandedRegion_vertex hS h0 hpoint hport hc hc1 (htrace d)
      ((R d).trace_subset (hstart d) hv)
  · intro d e hde z hz hz'
    exact P.expandedRegions_intersect hS h0 hport hc hc1 htrace hleaf hde
      ((R d).trace_subset (hstart d) hz) ((R e).trace_subset (hstart e) hz')
  · intro d
    exact (R d).trace_subset (hstart d)

end PLDrawing
end PlanarL1.Topology



end

end OAI
