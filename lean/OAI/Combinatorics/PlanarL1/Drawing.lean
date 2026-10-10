import OAI.Combinatorics.PlanarL1.Statement
import OAI.Combinatorics.PlanarL1.DiskCrossing

namespace OAI

section

namespace PlanarL1.Topology
open Set Metric

/-- The literal topological drawing, with its coordinates identified with the
complex plane. No polygonal or combinatorial planarity assumption is added. -/
structure Drawing {V : Type} (G : SimpleGraph V) where
  point : V → ℂ
  point_injective : Function.Injective point
  edge : ∀ u v, G.Adj u v → Path (point u) (point v)
  edge_injective : ∀ u v h, Function.Injective (edge u v h)
  interior_avoid : ∀ u v h (t : unitInterval) w,
    0<(t:ℝ) → (t:ℝ)<1 → edge u v h t ≠ point w
  interior_disjoint : ∀ u v h x y k (s t : unitInterval),
    0<(s:ℝ) → (s:ℝ)<1 → 0<(t:ℝ) → (t:ℝ)<1 →
    edge u v h s=edge x y k t → (u=x ∧ v=y) ∨ (u=y ∧ v=x)

lemma drawing_of_planar {V : Type} {G : SimpleGraph V} (h : IsPlanar G) :
    Nonempty (Drawing G) := by
  obtain ⟨p,a,hp,ha,hi,hv,hd⟩ := h
  let e := Complex.equivRealProdCLM.symm
  refine ⟨⟨fun v => e (p v),e.injective.comp hp,
    fun u v h => ⟨⟨fun t => e (a u v h t),e.continuous.comp (a u v h).continuous⟩,
      congrArg e (ha u v h).1,congrArg e (ha u v h).2⟩,?_,?_,?_⟩⟩
  · intro u v h
    exact e.injective.comp (hi u v h)
  · intro u v h t w ht ht' he
    exact hv u v h t w ht ht' (e.injective he)
  · intro u v h x y k s t hs hs' ht ht' he
    exact hd u v h x y k s t hs hs' ht ht' (e.injective he)

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

lemma point_on_edge_iff (u v : V) (h : G.Adj u v) (w : V) (t : unitInterval) :
    D.edge u v h t=D.point w ↔ (t=0 ∧ w=u) ∨ (t=1 ∧ w=v) := by
  constructor
  · intro he
    by_cases h0 : t=0
    · left
      refine ⟨h0,?_⟩
      rw [h0,Path.source] at he
      exact (D.point_injective he).symm
    by_cases h1 : t=1
    · right
      refine ⟨h1,?_⟩
      rw [h1,Path.target] at he
      exact (D.point_injective he).symm
    exact False.elim (D.interior_avoid u v h t w
      (lt_of_le_of_ne t.2.1 (by intro he; exact h0 (Subtype.ext he.symm)))
      (lt_of_le_of_ne t.2.2 (by intro he; exact h1 (Subtype.ext he))) he)
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp

/-- Away from the first/last third of an incident edge, every vertex is
uniformly separated from that edge. The set is closed even at both cutoffs. -/
def excludedTimes (w : V) (d : G.Dart) : Set unitInterval :=
  {t | (w≠d.fst ∨ (1/3:ℝ)≤(t:ℝ)) ∧ (w≠d.snd ∨ (t:ℝ)≤(2/3:ℝ))}

lemma excludedTimes_closed (w : V) (d : G.Dart) : IsClosed (excludedTimes w d) := by
  have hu : IsClosed {t : unitInterval | w≠d.fst} := by
    by_cases h : w≠d.fst <;> simp [h]
  have hv : IsClosed {t : unitInterval | w≠d.snd} := by
    by_cases h : w≠d.snd <;> simp [h]
  exact (hu.union (isClosed_le continuous_const continuous_subtype_val)).inter
    (hv.union (isClosed_le continuous_subtype_val continuous_const))

lemma excludedTimes_avoid (w : V) (d : G.Dart) :
    D.point w ∉ D.edge d.fst d.snd d.adj '' excludedTimes w d := by
  rintro ⟨t,ht,he⟩
  rcases (D.point_on_edge_iff _ _ _ _ t).mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rcases ht.1 with h | h
    · exact h rfl
    · norm_num at h
  · rcases ht.2 with h | h
    · exact h rfl
    · norm_num at h

variable [Fintype V]
/-- A compact forbidden set for a vertex disk: other vertices and the
parts of every drawn edge that must stay outside that disk. -/
def forbidden (w : V) : Set ℂ :=
  (⋃ v : {v : V // v≠w}, {D.point v.val}) ∪
    ⋃ d : G.Dart, D.edge d.fst d.snd d.adj '' excludedTimes w d

lemma forbidden_compact (w : V) : IsCompact (D.forbidden w) := by
  classical
  apply IsCompact.union
  · exact isCompact_iUnion (fun _ => isCompact_singleton)
  · exact isCompact_iUnion (fun d =>
      (excludedTimes_closed w d).isCompact.image (D.edge _ _ _).continuous)

omit [Fintype V] in
lemma forbidden_avoid (w : V) : D.point w ∉ D.forbidden w := by
  rintro (h | h)
  · obtain ⟨⟨v,hv⟩,he⟩ := mem_iUnion.mp h
    exact hv (D.point_injective (mem_singleton_iff.mp he).symm)
  · obtain ⟨d,hd⟩ := mem_iUnion.mp h
    exact D.excludedTimes_avoid w d hd

lemma vertex_disk (w : V) :
    ∃ r>0, ∀ z ∈ D.forbidden w, r<dist (D.point w) z := by
  have hopen := (D.forbidden_compact w).isClosed.isOpen_compl
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hopen (D.point w) (D.forbidden_avoid w)
  refine ⟨r/2,half_pos hr,fun z hz => ?_⟩
  have hnot : ¬dist z (D.point w)<r := fun h => hball h hz
  rw [dist_comm] at hnot
  linarith

/-- One common positive radius works for all vertices; arbitrary edge
oscillations and arbitrary straight-line distances between drawn vertices are
allowed. This radius is topological auxiliary data, not a metric edge scale. -/
lemma uniform_vertex_disks :
    ∃ r>0, ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h => exact ⟨1,by norm_num,fun w => isEmptyElim w⟩
  | inr h =>
    choose e he hs using D.vertex_disk
    let R := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty) e
    have hR : 0<R := (Finset.lt_inf'_iff _).mpr (fun w _ => he w)
    refine ⟨R/10,by positivity,fun w z hz => ?_⟩
    have hRw : R≤e w := Finset.inf'_le e (Finset.mem_univ w)
    have hz' := hs w z hz
    linarith

end Drawing

/-- Last exit from a closed disk before a specified later time. This works
for arbitrary continuous paths, including paths which oscillate infinitely
near their endpoint. No local straightness of a topological arc is assumed. -/
lemma path_lastExit {X : Type*} [MetricSpace X] {x y : X} (p : Path x y)
    {b r : ℝ} (hb : 0<b) (hr : 0<r)
    (hout : r<dist (p.extend b) x) :
    ∃ a : ℝ, 0<a ∧ a<b ∧ dist (p.extend a) x=r ∧
      ∀ t, a<t → t≤b → r<dist (p.extend t) x := by
  let S := Set.Icc 0 b ∩ {t : ℝ | dist (p.extend t) x≤r}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_le (p.continuous_extend.dist continuous_const) continuous_const)
  have h0 : (0:ℝ) ∈ S := by simp only [S,mem_inter_iff,mem_Icc,mem_ofPred_eq,
    Path.extend_zero,dist_self]; exact ⟨⟨le_rfl,hb.le⟩,hr.le⟩
  obtain ⟨a,ha,hamax⟩ := hS.exists_isGreatest ⟨0,h0⟩
  have hab : a<b := lt_of_le_of_ne ha.1.2 (by intro he; exact (not_le_of_gt hout) (he ▸ ha.2))
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hab.le
    (p.continuous_extend.dist continuous_const).continuousOn (⟨ha.2,hout.le⟩ :
      r ∈ Set.Icc (dist (p.extend a) x) (dist (p.extend b) x))
  have hta : t≤a := hamax ⟨⟨ha.1.1.trans ht.1,ht.2⟩,he.le⟩
  have har : dist (p.extend a) x=r := (le_antisymm hta ht.1) ▸ he
  have ha0 : 0<a := lt_of_le_of_ne ha.1.1 (by
    intro he
    rw [← he,Path.extend_zero,dist_self] at har
    exact hr.ne' har.symm)
  refine ⟨a,ha0,hab,har,fun t hat htb => ?_⟩
  by_contra! h
  exact (not_le_of_gt hat) (hamax ⟨⟨ha0.le.trans hat.le,htb⟩,h⟩)

lemma path_trimStart {X : Type*} [MetricSpace X] {x y : X} (p : Path x y)
    {b : unitInterval} {r : ℝ} (hb : 0<(b:ℝ)) (hr : 0<r)
    (hout : ∀ t : unitInterval, b≤t → r<dist (p t) x) :
    ∃ a : unitInterval, 0<(a:ℝ) ∧ a<b ∧ dist (p a) x=r ∧
      ∀ t : unitInterval, a<t → r<dist (p t) x := by
  have hb' : r<dist (p.extend b) x := by
    rw [p.extend_apply b.property]
    exact hout b le_rfl
  obtain ⟨a,ha0,hab,he,ht⟩ := path_lastExit p hb hr hb'
  let a' : unitInterval := ⟨a,ha0.le,hab.le.trans b.2.2⟩
  refine ⟨a',ha0,hab,?_,fun t hat => ?_⟩
  · change dist (p.extend (a':ℝ)) x=r at he
    rw [p.extend_apply a'.property] at he
    exact he
  · by_cases htb : t≤b
    · have ht' := ht t hat htb
      simpa only [p.extend_apply t.property] using ht'
    · exact hout t (le_of_not_ge htb)

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

lemma edge_mem_forbidden (w : V) (d : G.Dart) (t : unitInterval)
    (h : t ∈ excludedTimes w d) :
    D.edge d.fst d.snd d.adj t ∈ D.forbidden w :=
  Or.inr (mem_iUnion.mpr ⟨d,⟨t,h,rfl⟩⟩)

lemma point_mem_forbidden (w v : V) (h : v≠w) : D.point v ∈ D.forbidden w :=
  Or.inl (mem_iUnion.mpr ⟨⟨v,h⟩,rfl⟩)

/-- Truncate one actual drawn edge outside disjoint small vertex disks.
The middle arc stays outside every disk, with equality only at its own ends. -/
structure EdgeTrim (r : ℝ) (d : G.Dart) where
  first : unitInterval
  last : unitInterval
  first_pos : 0<(first:ℝ)
  first_lt : (first:ℝ)<1/3
  last_gt : (2/3:ℝ)<(last:ℝ)
  last_lt_one : (last:ℝ)<1
  first_sphere : dist (D.edge d.fst d.snd d.adj first) (D.point d.fst)=r
  last_sphere : dist (D.edge d.fst d.snd d.adj last) (D.point d.snd)=r
  after_first : ∀ t : unitInterval, first<t →
    r<dist (D.edge d.fst d.snd d.adj t) (D.point d.fst)
  before_last : ∀ t : unitInterval, t<last →
    r<dist (D.edge d.fst d.snd d.adj t) (D.point d.snd)

lemma edgeTrim_nonempty {r : ℝ} (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z) (d : G.Dart) :
    Nonempty (D.EdgeTrim r d) := by
  let p := D.edge d.fst d.snd d.adj
  let b : unitInterval := ⟨1/3,by norm_num,by norm_num⟩
  have hleft : ∀ t : unitInterval, b≤t → r<dist (p t) (D.point d.fst) := by
    intro t ht
    have hfor := D.edge_mem_forbidden d.fst d t
      ⟨Or.inr ht,Or.inl d.fst_ne_snd⟩
    have hh := hsep d.fst (p t) hfor
    rw [dist_comm] at hh
    linarith
  have hright : ∀ t : unitInterval, b≤t → r<dist (p.symm t) (D.point d.snd) := by
    intro t ht
    let t' : unitInterval := ⟨1-(t:ℝ),by linarith [t.2.2],by linarith [t.2.1]⟩
    have he : p.symm t=p t' := rfl
    have hfor := D.edge_mem_forbidden d.snd d t'
      ⟨Or.inl d.snd_ne_fst,Or.inr (by dsimp [t']; change (1/3:ℝ)≤(t:ℝ) at ht; linarith)⟩
    have hh := hsep d.snd (p t') hfor
    rw [dist_comm,← he] at hh
    linarith
  obtain ⟨a,ha0,hab,ha,haafter⟩ := path_trimStart p (by norm_num : 0<(b:ℝ)) hr hleft
  obtain ⟨z,hz0,hzb,hz,hzafter⟩ := path_trimStart p.symm (by norm_num : 0<(b:ℝ)) hr hright
  let last : unitInterval := ⟨1-(z:ℝ),by linarith [z.2.2],by linarith [z.2.1]⟩
  refine ⟨⟨a,last,ha0,hab,?_,?_,ha,?_,haafter,?_⟩⟩
  · change (1/3:ℝ)>(z:ℝ) at hzb
    change (2/3:ℝ)<1-(z:ℝ)
    linarith
  · change 1-(z:ℝ)<1
    linarith
  · exact hz
  · intro t ht
    let t' : unitInterval := ⟨1-(t:ℝ),by linarith [t.2.2],by linarith [t.2.1]⟩
    have ht' : z<t' := by
      change (t:ℝ)<1-(z:ℝ) at ht
      change (z:ℝ)<1-(t:ℝ)
      linarith
    have he : p.symm t'=p t := by
      change p ⟨1-(1-(t:ℝ)),_⟩=p t
      congr 1
      apply Subtype.ext
      dsimp
      ring
    simpa only [he] using hzafter t' ht'

namespace EdgeTrim
variable {D} {r : ℝ} {d : G.Dart} (T : D.EdgeTrim r d)

lemma first_lt_last : T.first<T.last := by
  have h := T.first_lt
  have h' := T.last_gt
  change (T.first:ℝ)<(T.last:ℝ)
  linarith

lemma middle_outside (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    (w : V) (t : unitInterval) (hft : T.first≤t) (htl : t≤T.last) :
    r≤dist (D.edge d.fst d.snd d.adj t) (D.point w) := by
  by_cases hw : w=d.fst
  · subst w
    rcases eq_or_lt_of_le hft with h | h
    · rw [← h,T.first_sphere]
    · exact (T.after_first t h).le
  by_cases hw' : w=d.snd
  · subst w
    rcases eq_or_lt_of_le htl with h | h
    · rw [h,T.last_sphere]
    · exact (T.before_last t h).le
  have hh := hsep w _ (D.edge_mem_forbidden w d t ⟨Or.inl hw,Or.inl hw'⟩)
  rw [dist_comm] at hh
  linarith

lemma middle_strict (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    (w : V) (t : unitInterval) (hft : T.first<t) (htl : t<T.last) :
    r<dist (D.edge d.fst d.snd d.adj t) (D.point w) := by
  by_cases hw : w=d.fst
  · subst w
    exact T.after_first t hft
  by_cases hw' : w=d.snd
  · subst w
    exact T.before_last t htl
  have hh := hsep w _ (D.edge_mem_forbidden w d t ⟨Or.inl hw,Or.inl hw'⟩)
  rw [dist_comm] at hh
  linarith
end EdgeTrim
end Drawing

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite chain of straight segments contained in a specified set. -/
def PolygonallyJoined (S : Set E) (x y : E) : Prop :=
  Relation.ReflTransGen (fun a b => segment ℝ a b ⊆ S) x y

lemma polygonallyJoined_of_path {S : Set E} (hS : IsOpen S) {x y : E}
    (p : Path x y) (hp : Set.range p ⊆ S) : PolygonallyJoined S x y := by
  classical
  let A := {z | z ∈ S ∧ PolygonallyJoined S x z}
  let B := S \ A
  have hA : IsOpen A := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hS z hz.1
    refine ⟨r,hr,fun w hw => ⟨hball hw,?_⟩⟩
    exact hz.2.tail ((convex_ball z r).segment_subset (by simpa using hr) hw |>.trans hball)
  have hB : IsOpen B := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hS z hz.1
    refine ⟨r,hr,fun w hw => ⟨hball hw,fun hwA => hz.2 ⟨hz.1,?_⟩⟩⟩
    exact hwA.2.tail ((convex_ball z r).segment_subset hw (by simpa using hr) |>.trans hball)
  have hd : Disjoint A B := Set.disjoint_left.mpr (fun z ha hb => hb.2 ha)
  have hu : Set.range p ⊆ A ∪ B := by
    intro z hz
    by_cases ha : z ∈ A
    · exact Or.inl ha
    · exact Or.inr ⟨hp hz,ha⟩
  have hne : (Set.range p ∩ A).Nonempty :=
    ⟨x,⟨0,p.source⟩,hp ⟨0,p.source⟩,Relation.ReflTransGen.refl⟩
  have hall := IsPreconnected.subset_left_of_subset_union hA hB hd hu hne
    (isPreconnected_range p.continuous)
  exact (hall ⟨1,p.target⟩).2

/-- Polygonal connectivity has literal finite-list witnesses. -/
lemma PolygonallyJoined.exists_chain {S : Set E} {x y : E}
    (h : PolygonallyJoined S x y) :
    ∃ l : List E, (x::l).IsChain (fun a b => segment ℝ a b ⊆ S) ∧
      (x::l).getLast (by simp)=y := by
  exact List.exists_isChain_cons_of_relationReflTransGen h

/-- Disjoint compact arcs can be simultaneously thickened, while avoiding
separate closed obstacles. No finiteness or regularity of the arcs themselves
beyond compactness is used. -/
lemma finite_disjoint_open_neighborhoods {ι X : Type*} [Fintype ι] [MetricSpace X]
    (K F : ι → Set X) (hK : ∀ i, IsCompact (K i)) (hF : ∀ i, IsClosed (F i))
    (hKF : ∀ i, Disjoint (K i) (F i)) (hKK : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧ Disjoint (U i) (F i)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  let O (i : ι) := F i ∪ ⋃ j : {j : ι // j≠i}, K j.val
  have hO (i : ι) : IsClosed (O i) :=
    (hF i).union (isClosed_iUnion_of_finite (fun j => (hK j).isClosed))
  have hKO (i : ι) : Disjoint (K i) (O i) := by
    apply Disjoint.union_right (hKF i)
    refine Set.disjoint_iUnion_right.mpr (fun j => ?_)
    exact hKK j.property.symm
  choose r hr hd using fun i => (hKO i).exists_thickenings (hK i) (hO i)
  refine ⟨fun i => Metric.thickening (r i) (K i),?_,?_⟩
  · intro i
    refine ⟨Metric.isOpen_thickening,Metric.self_subset_thickening (hr i) _,?_⟩
    exact (hd i).mono_right ((show F i ⊆ O i from Set.subset_union_left).trans
      (Metric.self_subset_thickening (hr i) _))
  · intro i j hij
    have hji : K j ⊆ O i := fun x hx => Or.inr (mem_iUnion.mpr ⟨⟨j,hij.symm⟩,hx⟩)
    have hij' : K i ⊆ O j := fun x hx => Or.inr (mem_iUnion.mpr ⟨⟨i,hij⟩,hx⟩)
    rcases le_total (r j) (r i) with h | h
    · exact (hd i).mono_right ((Metric.thickening_mono h _).trans
        (Metric.thickening_subset_of_subset _ hji))
    · exact ((hd j).mono_right ((Metric.thickening_mono h _).trans
        (Metric.thickening_subset_of_subset _ hij'))).symm

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric

/-- On a radial segment, the endpoint is the only point at its maximal
radius. This is valid in every real normed space, without strict convexity. -/
lemma radial_segment_boundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y z : E} {r : ℝ} (hr : 0<r) (hy : dist y x=r)
    (hz : z ∈ segment ℝ x y) (hlo : r≤dist z x) : z=y := by
  rw [segment_eq_image' ℝ x y] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have he : dist (x+t•(y-x)) x=t*r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    rw [← dist_eq_norm,hy]
  have ht1 : t=1 := le_antisymm ht.2 ((le_mul_iff_one_le_left hr).mp (by simpa [he] using hlo))
  simp [ht1]

lemma compact_segment_complex (x y : ℂ) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image' ℝ x y]
  exact isCompact_Icc.image (by fun_prop)

/-- Distinct radial heads on the same sphere intersect only at their center. -/
lemma radial_heads_intersect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y w z : E} {r : ℝ} (hr : 0<r) (hy : dist y x=r) (hw : dist w x=r)
    (hne : y≠w) (hz : z ∈ segment ℝ x y) (hz' : z ∈ segment ℝ x w) : z=x := by
  rw [segment_eq_image' ℝ x y] at hz
  rw [segment_eq_image' ℝ x w] at hz'
  obtain ⟨t,ht,rfl⟩ := hz
  obtain ⟨s,hs,he⟩ := hz'
  have hn := congrArg (fun q => dist q x) he
  simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg ht.1,abs_of_nonneg hs.1] at hn
  rw [← dist_eq_norm,← dist_eq_norm,hw,hy] at hn
  have hst : s=t := (mul_right_cancel₀ hr.ne' hn)
  subst s
  by_cases ht0 : t=0
  · simp [ht0]
  · have hvec := add_left_cancel he
    have hew := (smul_right_injective E ht0) hvec
    exact False.elim (hne (sub_left_inj.mp hew).symm)

/-- Choosing only the forward dart avoids treating the two independently
supplied oriented parametrizations as one geometric edge. -/
def ForwardDart {V : Type} [LinearOrder V] (G : SimpleGraph V) :=
  {d : G.Dart // d.fst<d.snd}

namespace ForwardDart
variable {V : Type} [LinearOrder V] {G : SimpleGraph V}

instance [Fintype V] [DecidableRel G.Adj] : Fintype (ForwardDart G) :=
  inferInstanceAs (Fintype {d : G.Dart // d.fst<d.snd})
lemma eq_of_endpoints (d e : ForwardDart G)
    (h : (d.val.fst=e.val.fst ∧ d.val.snd=e.val.snd) ∨
      (d.val.fst=e.val.snd ∧ d.val.snd=e.val.fst)) : d=e := by
  rcases h with h | h
  · apply Subtype.ext
    exact SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2)
  · have hd := d.property
    rw [h.1,h.2] at hd
    exact False.elim (not_lt_of_gt e.property hd)
end ForwardDart

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

namespace EdgeTrim
variable {D} {r : ℝ} {d : G.Dart} (T : D.EdgeTrim r d)
noncomputable def middle : Path (D.edge d.fst d.snd d.adj T.first)
    (D.edge d.fst d.snd d.adj T.last) :=
  (D.edge d.fst d.snd d.adj).subpath T.first T.last

lemma middle_range : Set.range T.middle=
    D.edge d.fst d.snd d.adj '' Set.Icc T.first T.last :=
  Path.range_subpath_of_le _ _ _ T.first_lt_last.le

lemma middle_compact : IsCompact (Set.range T.middle) :=
  isCompact_range T.middle.continuous

lemma middle_avoid_vertices (w : V) : D.point w ∉ Set.range T.middle := by
  rw [T.middle_range]
  rintro ⟨t,ht,he⟩
  exact D.interior_avoid _ _ _ t w (T.first_pos.trans_le ht.1)
    ((show (t:ℝ)≤T.last from ht.2).trans_lt T.last_lt_one) he

lemma middle_radial_head {e : G.Dart} (U : D.EdgeTrim r e) (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    (hne : ¬ ((d.fst=e.fst ∧ d.snd=e.snd) ∨ (d.fst=e.snd ∧ d.snd=e.fst))) :
    Disjoint (Set.range T.middle)
      (segment ℝ (D.point e.fst) (D.edge e.fst e.snd e.adj U.first)) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rw [T.middle_range] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have he := radial_segment_boundary hr U.first_sphere hz'
    (T.middle_outside hr hsep e.fst t ht.1 ht.2)
  exact hne (D.interior_disjoint _ _ _ _ _ _ t U.first
    (T.first_pos.trans_le ht.1) ((show (t:ℝ)≤T.last from ht.2).trans_lt T.last_lt_one)
    U.first_pos (by linarith [U.first_lt]) he)

lemma middle_radial_tail {e : G.Dart} (U : D.EdgeTrim r e) (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z)
    (hne : ¬ ((d.fst=e.fst ∧ d.snd=e.snd) ∨ (d.fst=e.snd ∧ d.snd=e.fst))) :
    Disjoint (Set.range T.middle)
      (segment ℝ (D.point e.snd) (D.edge e.fst e.snd e.adj U.last)) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rw [T.middle_range] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have he := radial_segment_boundary hr U.last_sphere hz'
    (T.middle_outside hr hsep e.snd t ht.1 ht.2)
  exact hne (D.interior_disjoint _ _ _ _ _ _ t U.last
    (T.first_pos.trans_le ht.1) ((show (t:ℝ)≤T.last from ht.2).trans_lt T.last_lt_one)
    (by linarith [U.last_gt]) U.last_lt_one he)
end EdgeTrim

variable [Fintype V] [LinearOrder V] {D} {r : ℝ} (T : ∀ d : ForwardDart G, D.EdgeTrim r d.val)

omit [Fintype V] in
lemma forward_middles_disjoint : Pairwise (fun d e : ForwardDart G =>
    Disjoint (Set.range (T d).middle) (Set.range (T e).middle)) := by
  intro d e hde
  apply Set.disjoint_left.mpr
  intro z hz hz'
  rw [(T d).middle_range] at hz
  rw [(T e).middle_range] at hz'
  obtain ⟨s,hs,rfl⟩ := hz
  obtain ⟨t,ht,he⟩ := hz'
  exact hde (ForwardDart.eq_of_endpoints d e (D.interior_disjoint _ _ _ _ _ _ s t
    ((T d).first_pos.trans_le hs.1) ((show (s:ℝ)≤(T d).last from hs.2).trans_lt (T d).last_lt_one)
    ((T e).first_pos.trans_le ht.1) ((show (t:ℝ)≤(T e).last from ht.2).trans_lt (T e).last_lt_one) he.symm))

/-- Obstacles for the middle of an edge: all vertices and the radial heads
of every other unoriented edge. -/
noncomputable def middleObstacle (d : ForwardDart G) : Set ℂ :=
  Set.range D.point ∪ ⋃ e : {e : ForwardDart G // e≠d},
    (segment ℝ (D.point e.val.val.fst)
      (D.edge e.val.val.fst e.val.val.snd e.val.val.adj (T e.val).first)) ∪
    (segment ℝ (D.point e.val.val.snd)
      (D.edge e.val.val.fst e.val.val.snd e.val.val.adj (T e.val).last))

lemma middleObstacle_closed (d : ForwardDart G) : IsClosed (D.middleObstacle T d) := by
  classical
  exact (Set.finite_range D.point).isClosed.union (isClosed_iUnion_of_finite (fun e =>
    (compact_segment_complex _ _).isClosed.union (compact_segment_complex _ _).isClosed))

omit [Fintype V] in
lemma middleObstacle_disjoint (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z) (d : ForwardDart G) :
    Disjoint (Set.range (T d).middle) (D.middleObstacle T d) := by
  apply Disjoint.union_right
  · apply Set.disjoint_left.mpr
    rintro z hz ⟨w,rfl⟩
    exact (T d).middle_avoid_vertices w hz
  · refine Set.disjoint_iUnion_right.mpr (fun e => ?_)
    have hne : ¬ ((d.val.fst=e.val.val.fst ∧ d.val.snd=e.val.val.snd) ∨
        (d.val.fst=e.val.val.snd ∧ d.val.snd=e.val.val.fst)) :=
      fun h => e.property (ForwardDart.eq_of_endpoints d e.val h).symm
    exact Disjoint.union_right ((T d).middle_radial_head (T e.val) hr hsep hne)
      ((T d).middle_radial_tail (T e.val) hr hsep hne)

/-- Every trimmed edge can be replaced by a literal finite segment chain,
inside mutually disjoint open tubes avoiding all other edge heads and all
vertices. This is the needed simultaneous polygonalization step. -/
lemma polygonal_middles (hr : 0<r)
    (hsep : ∀ w z, z ∈ D.forbidden w → 5*r<dist (D.point w) z) :
    ∃ U : ForwardDart G → Set ℂ,
      (∀ d, IsOpen (U d) ∧ Disjoint (U d) (D.middleObstacle T d) ∧
        PolygonallyJoined (U d)
          (D.edge d.val.fst d.val.snd d.val.adj (T d).first)
          (D.edge d.val.fst d.val.snd d.val.adj (T d).last)) ∧
      Pairwise (fun d e => Disjoint (U d) (U e)) := by
  classical
  obtain ⟨U,hU,hd⟩ := finite_disjoint_open_neighborhoods
    (fun d => Set.range (T d).middle) (D.middleObstacle T)
    (fun d => (T d).middle_compact) (D.middleObstacle_closed T)
    (D.middleObstacle_disjoint T hr hsep) (D.forward_middles_disjoint T)
  exact ⟨U,fun d => ⟨(hU d).1,(hU d).2.2,
    polygonallyJoined_of_path (hU d).1 (T d).middle (hU d).2.1⟩,hd⟩

end Drawing
end PlanarL1.Topology



end

end OAI
