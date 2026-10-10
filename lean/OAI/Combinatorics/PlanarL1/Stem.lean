import OAI.Combinatorics.PlanarL1.Retubing

namespace OAI

section



namespace PlanarL1.Topology
open Set Metric Filter

lemma segment_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : E} (hb : b∈segment ℝ a c) :
    segment ℝ a c=segment ℝ a b ∪ segment ℝ b c := by
  apply Set.Subset.antisymm
  · rw [segment_eq_image' ℝ] at hb ⊢
    obtain ⟨t,ht,rfl⟩ := hb
    rintro z ⟨u,hu,rfl⟩
    by_cases hut : u≤t
    · left
      by_cases ht0 : t=0
      · have hu0 : u=0 := by linarith [hu.1]
        simp only [hu0,zero_smul,add_zero]; exact left_mem_segment ℝ _ _
      rw [segment_eq_image' ℝ]
      refine ⟨u/t,⟨div_nonneg hu.1 ht.1,(div_le_one (lt_of_le_of_ne ht.1 (Ne.symm ht0))).mpr hut⟩,?_⟩
      have he : (u/t)*t=u := div_mul_cancel₀ u ht0
      simp only [add_sub_cancel_left,smul_smul,he]
    · right
      have htu : t<u := lt_of_not_ge hut
      have ht1 : t<1 := lt_of_lt_of_le htu hu.2
      rw [segment_eq_image' ℝ]
      refine ⟨(u-t)/(1-t),⟨div_nonneg (sub_nonneg.mpr htu.le) (sub_nonneg.mpr ht1.le),
        (div_le_one (sub_pos.mpr ht1)).mpr (by linarith [hu.2])⟩,?_⟩
      have hne : 1-t≠0 := ne_of_gt (sub_pos.mpr ht1)
      have he : t+((u-t)/(1-t))*(1-t)=u := by field_simp; ring
      calc a+t•(c-a)+((u-t)/(1-t))•(c-(a+t•(c-a)))
        = a+(t+((u-t)/(1-t))*(1-t))•(c-a) := by module
        _ = a+u•(c-a) := by rw [he]
  · exact Set.union_subset
      ((convex_segment a c).segment_subset (left_mem_segment ℝ _ _) hb)
      ((convex_segment a c).segment_subset hb (right_mem_segment ℝ _ _))

lemma convex_frontier_segment_at {S : Set ℂ} (hS : Convex ℝ S) (hop : IsOpen S)
    {a p q : ℂ} (ha : a∈S) (hp : p∈frontier S) (hq : q∈frontier S)
    (hseg : q∈segment ℝ a p) : q=p := by
  let f := AffineEquiv.constVAdd ℝ ℂ (-a)
  have hC : Convex ℝ (f '' S) := hS.affine_image f.toAffineMap
  have hO : IsOpen (f '' S) := f.toContinuousAffineEquiv.toHomeomorph.isOpenMap S hop
  have hzero : (0:ℂ)∈f '' S := ⟨a,ha,by simp [f]⟩
  have hfr (z : ℂ) (hz : z∈frontier S) : f z∈frontier (f '' S) := by
    rw [PLDrawing.affine_image_frontier]; exact ⟨z,hz,rfl⟩
  apply f.injective
  apply convex_frontier_segment hC (hO.mem_nhds hzero) (hfr p hp) (hfr q hq)
  have hs : f '' segment ℝ a p=segment ℝ (f a) (f p) := image_segment ℝ f.toAffineMap a p
  have hz : f q∈f '' segment ℝ a p := ⟨q,hseg,rfl⟩
  simpa only [hs,show f a=0 by simp [f]] using hz

namespace ExteriorPorts
variable {V : Type} {p target : V → ℂ} {B : Set V} {S : Set ℂ}
  (E : ExteriorPorts p target B S)

lemma spoke_intersection (hinj : Function.Injective p) (hS : Convex ℝ S) (hop : IsOpen S)
    {a : ℂ} (ha : a∈S) (hport : ∀ w∈B, p w∈frontier S)
    {v w : V} (hv : v∈B) (hw : w∈B) {z : ℂ}
    (hz : z∈segment ℝ a (p v)) (hz' : z∈E.region w) : v=w ∧ z=p v := by
  have he : z=p w := E.inside w hw z hz'
    (hS.closure.segment_subset (subset_closure ha) (frontier_subset_closure (hport v hv)) hz)
  have he' : p w=p v := convex_frontier_segment_at hS hop ha (hport v hv) (hport w hw)
    (he ▸ hz)
  exact ⟨(hinj he').symm,he.trans he'⟩

lemma spoke_disjoint (hinj : Function.Injective p) (hS : Convex ℝ S) (hop : IsOpen S)
    {a : ℂ} (ha : a∈S) (hport : ∀ w∈B, p w∈frontier S)
    {v w : V} (hv : v∈B) (hw : w∈B) (hvw : v≠w) :
    Disjoint (segment ℝ a (p v)) (E.region w) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact hvw (E.spoke_intersection hinj hS hop ha hport hv hw hz hz').1

noncomputable def restrict (C : Set V) (hC : C ⊆ B) : ExteriorPorts p target C S where
  region := E.region
  compact w hw := E.compact w (hC hw)
  start w hw := E.start w (hC hw)
  joined w hw := E.joined w (hC hw)
  inside w hw := E.inside w (hC hw)
  disjoint w hw u hu := E.disjoint w (hC hw) u (hC hu)

lemma obstacles_closed [Finite V] {v : V} {K U : Set ℂ} (hK : IsClosed K) (hU : IsClosed U) :
    IsClosed (K ∪ U ∪ ⋃ w : {w // w∈B ∧ w≠v}, E.region w) :=
  (hK.union hU).union (isClosed_iUnion_of_finite (fun w => (E.compact w w.property.1).isClosed))

end ExteriorPorts

namespace SegmentChain
variable {S : Set ℂ} {x y : ℂ} {n : ℕ} (P : SegmentChain S x y (n+1))

lemma piece_subset_trace (i : ℕ) (hi : i<n+1) :
    segment ℝ (P.vertex i) (P.vertex (i+1)) ⊆ P.trace := by
  intro z hz
  exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i,hi⟩,hz⟩)

lemma first_segment_subset : segment ℝ x (P.vertex 1) ⊆ P.trace := by
  rw [P.tail_trace]; exact Set.subset_union_left

lemma cut_not_start (hP : P.IsSimple) {t : ℝ} (ht : 0<t) (_ht1 : t≤1) :
    x+t•(P.vertex 1-x)≠x := by
  intro he
  have he' : t•(P.vertex 1-x)=0 := add_left_cancel (he.trans (add_zero x).symm)
  rcases smul_eq_zero.mp he' with he'|he'
  · exact (ne_of_gt ht) he'
  · exact P.first_ne hP (sub_eq_zero.mp he')

lemma cut_not_next (hP : P.IsSimple) {t : ℝ} (ht : t<1) :
    x+t•(P.vertex 1-x)≠P.vertex 1 := by
  intro he
  have he' : (1-t)•(P.vertex 1-x)=0 := by
    calc (1-t)•(P.vertex 1-x)=P.vertex 1-(x+t•(P.vertex 1-x)) := by module
      _ = 0 := by rw [he,sub_self]
  rcases smul_eq_zero.mp he' with he'|he'
  · exact (ne_of_gt (sub_pos.mpr ht)) he'
  · exact P.first_ne hP (sub_eq_zero.mp he')

lemma cut_avoids_start (hP : P.IsSimple) {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    x∉(P.cutFirst (x+t•(P.vertex 1-x)) (by rw [segment_eq_image' ℝ]; exact ⟨t,⟨ht.le,ht1⟩,rfl⟩)).trace := by
  rw [P.cutFirst_trace]
  rintro (hx|hx)
  · rw [segment_eq_image' ℝ] at hx
    obtain ⟨u,hu,he⟩ := hx
    dsimp only at he
    have he' : (t+u*(1-t))•(P.vertex 1-x)=0 := by
      calc (t+u*(1-t))•(P.vertex 1-x)
          = (x+t•(P.vertex 1-x)+u•(P.vertex 1-(x+t•(P.vertex 1-x))))-x := by module
        _ = 0 := by rw [he,sub_self]
    rcases smul_eq_zero.mp he' with he'|he'
    · have : 0<t+u*(1-t) := lt_of_lt_of_le ht (le_add_of_nonneg_right (mul_nonneg hu.1 (sub_nonneg.mpr ht1)))
      exact (ne_of_gt this) he'
    · exact P.first_ne hP (sub_eq_zero.mp he')
  · exact P.start_not_tail hP hx

/-- A literal cut of the first polygonal piece at the boundary of a convex
neighborhood. All of the residual path is outside, except for that port. -/
lemma exit_frontier (hP : P.IsSimple) {T : Set ℂ} (hT : Convex ℝ T) (hop : IsOpen T)
    (hx : x∈T) (htail : Disjoint (closure T) P.tail.trace) :
    ∃ q : ℂ, ∃ hq : q∈segment ℝ x (P.vertex 1),
      q∈frontier T ∧ q≠P.vertex 1 ∧ q≠x ∧
      (∀ z∈(P.cutFirst q hq).trace, z∈closure T → z=q) := by
  have hyout : P.vertex 1∉closure T := fun hy =>
    Set.disjoint_left.mp htail hy P.tail.start_mem_trace
  obtain ⟨t,ht,ht1,htfr,hin,hout⟩ := convex_segment_cut hT hop hx hyout
  let q := x+t•(P.vertex 1-x)
  have hq : q∈segment ℝ x (P.vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨t,⟨ht.le,ht1.le⟩,rfl⟩
  refine ⟨q,hq,htfr,P.cut_not_next hP ht1,P.cut_not_start hP ht ht1.le,?_⟩
  intro z hz hzT
  rw [P.cutFirst_trace] at hz
  rcases hz with hz|hz
  · rw [segment_eq_image' ℝ] at hz
    obtain ⟨u,hu,he⟩ := hz
    dsimp only at he
    by_cases hu0 : u=0
    · simpa only [hu0,zero_smul,add_zero] using he.symm
    · have hu' : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hgt : t<t+u*(1-t) := lt_add_of_pos_right _ (mul_pos hu' (sub_pos.mpr ht1))
      apply False.elim (hout (t+u*(1-t)) hgt _)
      have he' : x+(t+u*(1-t))•(P.vertex 1-x)=z := by
        calc x+(t+u*(1-t))•(P.vertex 1-x)=q+u•(P.vertex 1-q) := by dsimp only [q]; module
          _ = z := he
      exact he'.symm ▸ hzT
  · exact False.elim (Set.disjoint_left.mp htail hzT hz)

end SegmentChain
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter

variable {V : Type} [LinearOrder V] {G : SimpleGraph V} {B : Set V}

/-- A literal finite polyline core in a bounded convex disk, with specified
leaf ports on its boundary. These data are constructed by the surgeries. -/
structure DiskCore (G : SimpleGraph V) (B : Set V) where
  drawing : PLDrawing G
  disk : Set ℂ
  center : ℂ
  convex : Convex ℝ disk
  isOpen : IsOpen disk
  bounded : Bornology.IsBounded disk
  center_mem : center∈disk
  point_mem : ∀ w, drawing.point w∈closure disk
  trace_mem : ∀ d, (drawing.chain d).trace ⊆ closure disk
  port : ∀ w∈B, drawing.point w∈frontier disk

namespace DiskCore
variable (C : DiskCore G B)

noncomputable def restrict (B' : Set V) (hB : B' ⊆ B) : DiskCore G B' :=
  { C with port := fun w hw => C.port w (hB hw) }

lemma spoke_subset {v : V} : segment ℝ C.center (C.drawing.point v) ⊆ closure C.disk :=
  C.convex.closure.segment_subset (subset_closure C.center_mem) (C.point_mem v)

/-- Align the first residual piece with a new disk center, without consuming
any bend. A thin capsule avoids every other stem and the fixed obstacle. -/
lemma align [Finite V] {target : V → ℂ}
    (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K)
    {n : ℕ} (P : SegmentChain (E.region v) (C.drawing.point v) (target v) (n+1))
    (hP : P.IsSimple) :
    ∃ C' : DiskCore G B,
    ∃ E' : ExteriorPorts C'.drawing.point target B C'.disk,
    ∃ P' : SegmentChain (E'.region v) (C'.drawing.point v) (target v) (n+1),
      P'.IsSimple ∧ C'.drawing.point v∈segment ℝ C'.center (P'.vertex 1) ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  classical
  let x := C.drawing.point v
  let m := x+(1/2:ℝ)•(P.vertex 1-x)
  have hm : m∈segment ℝ x (P.vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨1/2,by norm_num,rfl⟩
  let U := (P.cutFirst m hm).trace
  have hU : IsCompact U := (P.cutFirst m hm).trace_compact
  have hUsub : U ⊆ E.region v := (P.cutFirst m hm).trace_subset (P.trace_subset (E.start v hv) (P.cutFirst_subset m hm (P.cutFirst m hm).start_mem_trace))
  have hxU : x∉U := P.cut_avoids_start hP (by norm_num) (by norm_num)
  let F := K ∪ U ∪ ⋃ w : {w // w∈B ∧ w≠v}, E.region w
  have hF : IsClosed F := E.obstacles_closed hK hU.isClosed
  have hdisj : Disjoint (segment ℝ C.center x) F := by
    apply Set.disjoint_left.mpr
    intro z hz hzF
    rcases hzF with (hzK|hzU)|hzE
    · exact Set.disjoint_left.mp hCK (C.spoke_subset hz) hzK
    · have he := E.spoke_intersection C.drawing.point_injective C.convex C.isOpen
        C.center_mem C.port hv hv hz (hUsub hzU)
      exact hxU (show C.drawing.point v∈U from he.2 ▸ hzU)
    · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzE
      exact w.property.2 (E.spoke_intersection C.drawing.point_injective C.convex C.isOpen
        C.center_mem C.port hv w.property.1 hz hw).1.symm
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding hF hdisj
  have hxT : x∈T := hseg (right_mem_segment ℝ _ _)
  have haT : C.center∈T := hseg (left_mem_segment ℝ _ _)
  have htail : Disjoint (closure T) P.tail.trace := by
    apply hd.mono_right
    intro z hz
    exact Or.inl (Or.inr (by change z∈(P.cutFirst m hm).trace; rw [P.cutFirst_trace]; exact Or.inr hz))
  obtain ⟨q,hq,hqfr,hqne,hqnx,hqin⟩ := P.exit_frontier hP hT hTop hxT htail
  let R := P.cutFirst q hq
  have hother (w : V) (hw : w∈B) (he : w≠v) : Disjoint (closure T) (E.region w) :=
    hd.mono_right (fun z hz => Or.inr (Set.mem_iUnion.mpr ⟨⟨w,hw,he⟩,hz⟩))
  obtain ⟨Q,hQ⟩ := C.drawing.retube_at C.convex C.isOpen C.center_mem C.bounded
    C.point_mem C.trace_mem C.port hleaf hv hT hTop haT hxT (frontier_subset_closure hqfr)
    (fun w hw he hz => Set.disjoint_left.mp (hother w hw he) hz (E.start w hw))
    (fun z hz hzS => E.inside v hv z
      (P.trace_subset (E.start v hv) (P.first_segment_subset ((convex_segment x (P.vertex 1)).segment_subset
        (left_mem_segment ℝ _ _) hq hz))) hzS)
  let C' : DiskCore G B := ⟨Q,T,x,hT,hTop,hTb,hxT,hQ.point_mem,hQ.trace_mem,by
    intro w hw
    by_cases he : w=v
    · subst w; rw [hQ.selected]; exact hqfr
    · exact hQ.on_frontier w hw he⟩
  let E' : ExteriorPorts C'.drawing.point target B C'.disk := E.update (PortFrame.ofMove hQ)
    C.drawing.point_injective C.port hv hother R.trace_compact R.start_mem_trace
    (R.trace_subset (P.trace_subset (E.start v hv) (P.first_segment_subset hq))) hqin R.joined_trace
  have hE' : E'.region v=R.trace := by simp [E',ExteriorPorts.update,ExteriorPorts.updatedRegion]
  have hpoint : C'.drawing.point v=q := hQ.selected
  let R' : SegmentChain (E'.region v) (C'.drawing.point v) (target v) (n+1) :=
    ⟨R.vertex,R.start.trans hpoint.symm,R.finish,fun i hi z hz =>
      hE'.symm ▸ R.piece_subset_trace i hi hz⟩
  refine ⟨C',E',R',P.cutFirst_simple hP q hq hqne,?_,
    hd.mono_right (fun z hz => Or.inl (Or.inl hz)),?_⟩
  · change C'.drawing.point v∈segment ℝ x (P.vertex 1)
    rw [hpoint]; exact hq
  · intro w hw z hz hzK
    by_cases he : w=v
    · subst w; rw [hE'] at hz
      exact R.trace_subset (P.trace_subset (E.start v hv) (P.first_segment_subset hq)) hz
    · change z∈ExteriorPorts.updatedRegion E Q.point v R.trace w at hz
      simp only [ExteriorPorts.updatedRegion,ite_eq_right he] at hz
      rcases hz with hz|hz
      · exact False.elim (Set.disjoint_left.mp hCK (hQ.tail_old w hw he hz) hzK)
      · exact hz

end DiskCore
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter
variable {V : Type} [LinearOrder V] [Finite V] {G : SimpleGraph V} {B : Set V}
namespace DiskCore
variable (C : DiskCore G B) {target : V → ℂ}

lemma finish_stem (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K) (hEK : Disjoint (E.region v) K)
    (hsegE : segment ℝ (C.drawing.point v) (target v) ⊆ E.region v)
    (hrad : C.drawing.point v∈segment ℝ C.center (target v)) :
    ∃ C' : DiskCore G (B \ {v}),
    ∃ E' : ExteriorPorts C'.drawing.point target (B \ {v}) C'.disk,
      C'.drawing.point v=target v ∧ C'.drawing.point v∈C'.disk ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B \ {v}, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  classical
  let F := K ∪ ⋃ w : {w // w∈B ∧ w≠v}, E.region w
  have hF : IsClosed F := hK.union
    (isClosed_iUnion_of_finite (fun w => (E.compact w w.property.1).isClosed))
  have hdisj : Disjoint (segment ℝ C.center (target v)) F := by
    rw [segment_split hrad]
    apply Disjoint.union_left
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with hzK|hzE
      · exact Set.disjoint_left.mp hCK (C.spoke_subset hz) hzK
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzE
        exact Set.disjoint_left.mp (E.spoke_disjoint C.drawing.point_injective C.convex
          C.isOpen C.center_mem C.port hv w.property.1 (Ne.symm w.property.2)) hz hw
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with hzK|hzE
      · exact Set.disjoint_left.mp hEK (hsegE hz) hzK
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzE
        exact Set.disjoint_left.mp (E.disjoint v hv w w.property.1 (Ne.symm w.property.2)) (hsegE hz) hw
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding hF hdisj
  have hqT : target v∈T := hseg (right_mem_segment ℝ _ _)
  have hxT : C.drawing.point v∈T := hseg hrad
  have haT : C.center∈T := hseg (left_mem_segment ℝ _ _)
  have hother (w : V) (hw : w∈B) (he : w≠v) : Disjoint (closure T) (E.region w) :=
    hd.mono_right (fun z hz => Or.inr (Set.mem_iUnion.mpr ⟨⟨w,hw,he⟩,hz⟩))
  obtain ⟨Q,hQ⟩ := C.drawing.retube_at C.convex C.isOpen C.center_mem C.bounded
    C.point_mem C.trace_mem C.port hleaf hv hT hTop haT hxT (subset_closure hqT)
    (fun w hw he hz => Set.disjoint_left.mp (hother w hw he) hz (E.start w hw))
    (fun z hz hzS => E.inside v hv z (hsegE hz) hzS)
  let C' : DiskCore G (B \ {v}) := ⟨Q,T,target v,hT,hTop,hTb,hqT,hQ.point_mem,hQ.trace_mem,
    fun w hw => hQ.on_frontier w hw.1 hw.2⟩
  let E₀ := E.update (PortFrame.ofMove hQ) C.drawing.point_injective C.port hv hother
    isCompact_singleton (show target v∈({target v}:Set ℂ) from rfl)
    (Set.singleton_subset_iff.mpr (E.end_mem v hv))
    (fun z hz _ => hz) (Relation.ReflTransGen.refl)
  let E' : ExteriorPorts C'.drawing.point target (B \ {v}) C'.disk :=
    E₀.restrict (B \ {v}) Set.sdiff_subset
  refine ⟨C',E',hQ.selected,hQ.selected.symm ▸ hqT,hd.mono_right Set.subset_union_left,?_⟩
  intro w hw z hz hzK
  change z∈ExteriorPorts.updatedRegion E Q.point v {target v} w at hz
  simp only [ExteriorPorts.updatedRegion,ite_eq_right (show w≠v from hw.2)] at hz
  rcases hz with hz|hz
  · exact False.elim (Set.disjoint_left.mp hCK (hQ.tail_old w hw.1 hw.2 hz) hzK)
  · exact hz

/-- Consuming one radial piece and cutting the next strictly decreases the
number of residual polygonal pieces. All other external stems remain disjoint. -/
lemma bend_stem (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K)
    (hEK : ∀ z∈E.region v, z∈K → z=target v)
    {n : ℕ} (P : SegmentChain (E.region v) (C.drawing.point v) (target v) (n+1+1))
    (hP : P.IsSimple) (hrad : C.drawing.point v∈segment ℝ C.center (P.vertex 1)) :
    ∃ C' : DiskCore G B,
    ∃ E' : ExteriorPorts C'.drawing.point target B C'.disk,
    ∃ P' : SegmentChain (E'.region v) (C'.drawing.point v) (target v) (n+1),
      P'.IsSimple ∧ C'.drawing.point v∈segment ℝ C'.center (P'.vertex 1) ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  classical
  let x := C.drawing.point v
  let y := P.vertex 1
  let R := P.tail
  have hR : R.IsSimple := P.tail_simple hP
  let m := y+(1/2:ℝ)•(R.vertex 1-y)
  have hm : m∈segment ℝ y (R.vertex 1) := by
    rw [segment_eq_image' ℝ]; exact ⟨1/2,by norm_num,rfl⟩
  let U := (R.cutFirst m hm).trace
  have hU : IsCompact U := (R.cutFirst m hm).trace_compact
  have hUtail : U ⊆ P.tail.trace := R.cutFirst_subset m hm
  have htailP : P.tail.trace ⊆ P.trace := by rw [P.tail_trace]; exact Set.subset_union_right
  have hUsub : U ⊆ E.region v := hUtail.trans (htailP.trans (P.trace_subset (E.start v hv)))
  have hxU : x∉U := fun hx => P.start_not_tail hP (hUtail hx)
  have hyU : y∉U := R.cut_avoids_start hR (by norm_num) (by norm_num)
  have hheadE : segment ℝ x y ⊆ E.region v := P.first_segment_subset.trans (P.trace_subset (E.start v hv))
  let F := K ∪ U ∪ ⋃ w : {w // w∈B ∧ w≠v}, E.region w
  have hF : IsClosed F := E.obstacles_closed hK hU.isClosed
  have hdisj : Disjoint (segment ℝ C.center y) F := by
    rw [segment_split hrad]
    apply Disjoint.union_left
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with (hzK|hzU)|hzE
      · exact Set.disjoint_left.mp hCK (C.spoke_subset hz) hzK
      · have he := E.spoke_intersection C.drawing.point_injective C.convex C.isOpen
          C.center_mem C.port hv hv hz (hUsub hzU)
        exact hxU (show C.drawing.point v∈U from he.2 ▸ hzU)
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzE
        exact w.property.2 (E.spoke_intersection C.drawing.point_injective C.convex C.isOpen
          C.center_mem C.port hv w.property.1 hz hw).1.symm
    · apply Set.disjoint_left.mpr
      intro z hz hzF
      rcases hzF with (hzK|hzU)|hzE
      · exact P.finish_not_first hP ((hEK z (hheadE hz) hzK) ▸ hz)
      · have he := P.head_tail_intersection hP hz (hUtail hzU)
        exact hyU (show P.vertex 1∈U from he ▸ hzU)
      · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzE
        exact Set.disjoint_left.mp (E.disjoint v hv w w.property.1 (Ne.symm w.property.2)) (hheadE hz) hw
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding hF hdisj
  have hyT : y∈T := hseg (right_mem_segment ℝ _ _)
  have hxT : x∈T := hseg hrad
  have haT : C.center∈T := hseg (left_mem_segment ℝ _ _)
  have htail : Disjoint (closure T) R.tail.trace := by
    apply hd.mono_right
    intro z hz
    exact Or.inl (Or.inr (by change z∈(R.cutFirst m hm).trace; rw [R.cutFirst_trace]; exact Or.inr hz))
  obtain ⟨q,hq,hqfr,hqne,hqny,hqin⟩ := R.exit_frontier hR hT hTop hyT htail
  let A := R.cutFirst q hq
  have hother (w : V) (hw : w∈B) (he : w≠v) : Disjoint (closure T) (E.region w) :=
    hd.mono_right (fun z hz => Or.inr (Set.mem_iUnion.mpr ⟨⟨w,hw,he⟩,hz⟩))
  obtain ⟨Q,hQ⟩ := C.drawing.retube_at C.convex C.isOpen C.center_mem C.bounded
    C.point_mem C.trace_mem C.port hleaf hv hT hTop haT hxT (subset_closure hyT)
    (fun w hw he hz => Set.disjoint_left.mp (hother w hw he) hz (E.start w hw))
    (fun z hz hzS => E.inside v hv z (hheadE hz) hzS)
  have hnextTail : segment ℝ y q ⊆ P.tail.trace :=
    ((convex_segment y (R.vertex 1)).segment_subset (left_mem_segment ℝ _ _) hq).trans R.first_segment_subset
  have hmeet (z : ℂ) (hz : z∈closure C.disk ∪ segment ℝ x y) (hn : z∈segment ℝ y q) : z=y := by
    rcases hz with hz|hz
    · have he := E.inside v hv z (P.trace_subset (E.start v hv) (htailP (hnextTail hn))) hz
      exact False.elim (P.start_not_tail hP (he ▸ hnextTail hn))
    · exact P.head_tail_intersection hP hz (hnextTail hn)
  have hvertex (w : V) (hw : Q.point w∈segment ℝ y q) : w=v := by
    apply Q.point_injective
    exact (hmeet _ (hQ.point_control w) hw).trans hQ.selected.symm
  have hcross (d : ForwardDart G) (z : ℂ) (hz : z∈(Q.chain d).trace) (hz' : z∈segment ℝ y q) : z=Q.point v :=
    (hmeet z (hQ.trace_control d hz) hz').trans hQ.selected.symm
  obtain ⟨Q',hpQ',hrQ'⟩ := Q.move_leaf (hleaf v hv)
    (right_mem_segment ℝ y q) hvertex hcross
    (show PolygonallyJoined (segment ℝ y q) (Q.point v) q from
      hQ.selected.symm ▸ Relation.ReflTransGen.single Set.Subset.rfl)
  have hpv : Q'.point v=q := by rw [congrFun hpQ']; simp [PLDrawing.movedPoint]
  have hpw (w : V) (he : w≠v) : Q'.point w=Q.point w := by
    rw [congrFun hpQ']; simp [PLDrawing.movedPoint,he]
  have hnT : segment ℝ y q ⊆ closure T :=
    hT.closure.segment_subset (subset_closure hyT) (frontier_subset_closure hqfr)
  let C' : DiskCore G B := ⟨Q',T,y,hT,hTop,hTb,hyT,
    (by intro w; by_cases he : w=v
        · subst w; rw [hpv]; exact frontier_subset_closure hqfr
        · rw [hpw w he]; exact hQ.point_mem w),
    (by intro d z hz; rcases hrQ' d hz with hz|hz
        · exact hQ.trace_mem d hz
        · exact hnT hz.2),
    (by intro w hw; by_cases he : w=v
        · subst w; rw [hpv]; exact hqfr
        · rw [hpw w he]; exact hQ.on_frontier w hw he)⟩
  have hframe : PortFrame C.drawing.point Q'.point B v q C.disk T :=
    (PortFrame.ofMove hQ).repoint hpv hpw
  have hA : A.trace ⊆ E.region v := (R.cutFirst_subset q hq).trans (htailP.trans (P.trace_subset (E.start v hv)))
  let E' : ExteriorPorts C'.drawing.point target B C'.disk := E.update hframe
    C.drawing.point_injective C.port hv hother A.trace_compact A.start_mem_trace hA hqin A.joined_trace
  have hE' : E'.region v=A.trace := by simp [E',ExteriorPorts.update,ExteriorPorts.updatedRegion]
  let A' : SegmentChain (E'.region v) (C'.drawing.point v) (target v) (n+1) :=
    ⟨A.vertex,A.start.trans hpv.symm,A.finish,fun i hi z hz => hE'.symm ▸ A.piece_subset_trace i hi hz⟩
  refine ⟨C',E',A',R.cutFirst_simple hR q hq hqne,?_,
    hd.mono_right (fun z hz => Or.inl (Or.inl hz)),?_⟩
  · change Q'.point v∈segment ℝ y (R.vertex 1)
    rw [hpv]; exact hq
  · intro w hw z hz hzK
    by_cases he : w=v
    · subst w; rw [hE'] at hz; exact hA hz
    · change z∈ExteriorPorts.updatedRegion E Q'.point v A.trace w at hz
      simp only [ExteriorPorts.updatedRegion,ite_eq_right he] at hz
      rcases hz with hz|hz
      · exact False.elim (Set.disjoint_left.mp hCK (hframe.tail_old w hw he hz) hzK)
      · exact hz

/-- A radial initial piece plus the finitely many bends of a simple polygonal
stem can be swallowed while the other stems remain genuine exterior routes. -/
lemma absorb_radial (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K) (hEK : Disjoint (E.region v) K)
    {n : ℕ} (P : SegmentChain (E.region v) (C.drawing.point v) (target v) (n+1))
    (hP : P.IsSimple) (hrad : C.drawing.point v∈segment ℝ C.center (P.vertex 1)) :
    ∃ C' : DiskCore G (B \ {v}),
    ∃ E' : ExteriorPorts C'.drawing.point target (B \ {v}) C'.disk,
      C'.drawing.point v=target v ∧ C'.drawing.point v∈C'.disk ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B \ {v}, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  induction n generalizing C with
  | zero =>
    apply C.finish_stem E hleaf hv hK hCK hEK
    · have hs := P.first_segment_subset.trans (P.trace_subset (E.start v hv))
      simpa only [P.finish] using hs
    · simpa only [P.finish] using hrad
  | succ n ih =>
    obtain ⟨C₁,E₁,P₁,hP₁,hr₁,hC₁,hprotect₁⟩ := C.bend_stem E hleaf hv hK hCK
      (fun z hz hzK => False.elim (Set.disjoint_left.mp hEK hz hzK)) P hP hrad
    have hE₁ : Disjoint (E₁.region v) K := Set.disjoint_left.mpr (fun z hz hzK =>
      Set.disjoint_left.mp hEK (hprotect₁ v hv z hz hzK) hzK)
    obtain ⟨C₂,E₂,hp₂,hint₂,hC₂,hprotect₂⟩ := ih C₁ E₁ hC₁ hE₁ P₁ hP₁ hr₁
    exact ⟨C₂,E₂,hp₂,hint₂,hC₂,fun w hw z hz hzK =>
      hprotect₁ w hw.1 z (hprotect₂ w hw z hz hzK) hzK⟩

/-- Absorb an arbitrary finite polygonal exterior stem into the disk. The
selected leaf reaches its actual exterior target, which becomes interior;
other ports and their external connections survive, without introducing
new intersections with any fixed closed obstacle disjoint from the route. -/
lemma absorb_stem (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K) (hEK : Disjoint (E.region v) K) :
    ∃ C' : DiskCore G (B \ {v}),
    ∃ E' : ExteriorPorts C'.drawing.point target (B \ {v}) C'.disk,
      C'.drawing.point v=target v ∧ C'.drawing.point v∈C'.disk ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B \ {v}, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  obtain ⟨n,P,hP⟩ := (E.joined v hv).exists_simple_segmentChain
  cases n with
  | zero =>
    have he : C.drawing.point v=target v := P.start.symm.trans P.finish
    apply C.finish_stem E hleaf hv hK hCK hEK
    · rw [he,segment_same]; exact Set.singleton_subset_iff.mpr (E.end_mem v hv)
    · rw [he]; exact right_mem_segment ℝ _ _
  | succ n =>
    obtain ⟨C₁,E₁,P₁,hP₁,hr₁,hC₁,hprotect₁⟩ := C.align E hleaf hv hK hCK P hP
    have hE₁ : Disjoint (E₁.region v) K := Set.disjoint_left.mpr (fun z hz hzK =>
      Set.disjoint_left.mp hEK (hprotect₁ v hv z hz hzK) hzK)
    obtain ⟨C₂,E₂,hp₂,hint₂,hC₂,hprotect₂⟩ := C₁.absorb_radial E₁ hleaf hv hK hC₁ hE₁ P₁ hP₁ hr₁
    exact ⟨C₂,E₂,hp₂,hint₂,hC₂,fun w hw z hz hzK =>
      hprotect₁ w hw.1 z (hprotect₂ w hw z hz hzK) hzK⟩

end DiskCore
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set
variable {V : Type} [LinearOrder V] [Finite V] {G : SimpleGraph V} {B : Set V}
namespace DiskCore
variable (C : DiskCore G B) {target : V → ℂ}

/-- Before the last radial piece is swallowed, all of a closed external
barrier, including the target vertex itself, can remain outside the disk. -/
lemma prepare_radial (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K)
    (hEK : ∀ z∈E.region v, z∈K → z=target v)
    {n : ℕ} (P : SegmentChain (E.region v) (C.drawing.point v) (target v) (n+1))
    (hP : P.IsSimple) (hrad : C.drawing.point v∈segment ℝ C.center (P.vertex 1)) :
    ∃ C' : DiskCore G B,
    ∃ E' : ExteriorPorts C'.drawing.point target B C'.disk,
      segment ℝ (C'.drawing.point v) (target v) ⊆ E'.region v ∧
      C'.drawing.point v∈segment ℝ C'.center (target v) ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  induction n generalizing C with
  | zero =>
    refine ⟨C,E,?_,?_,hCK,fun _ _ _ hz _ => hz⟩
    · have hs := P.first_segment_subset.trans (P.trace_subset (E.start v hv))
      simpa only [P.finish] using hs
    · simpa only [P.finish] using hrad
  | succ n ih =>
    obtain ⟨C₁,E₁,P₁,hP₁,hr₁,hC₁,hprotect₁⟩ := C.bend_stem E hleaf hv hK hCK hEK P hP hrad
    have hE₁ : ∀ z∈E₁.region v, z∈K → z=target v := fun z hz hzK =>
      hEK z (hprotect₁ v hv z hz hzK) hzK
    obtain ⟨C₂,E₂,hseg₂,hr₂,hC₂,hprotect₂⟩ := ih C₁ E₁ hC₁ hE₁ P₁ hP₁ hr₁
    exact ⟨C₂,E₂,hseg₂,hr₂,hC₂,fun w hw z hz hzK =>
      hprotect₁ w hw z (hprotect₂ w hw z hz hzK) hzK⟩

lemma prepare_stem (E : ExteriorPorts C.drawing.point target B C.disk)
    (hleaf : ∀ w∈B, ∀ u u', G.Adj w u → G.Adj w u' → u=u')
    {v : V} (hv : v∈B) {K : Set ℂ} (hK : IsClosed K)
    (hCK : Disjoint (closure C.disk) K) (htK : target v∈K)
    (hEK : ∀ z∈E.region v, z∈K → z=target v) :
    ∃ C' : DiskCore G B,
    ∃ E' : ExteriorPorts C'.drawing.point target B C'.disk,
      segment ℝ (C'.drawing.point v) (target v) ⊆ E'.region v ∧
      C'.drawing.point v∈segment ℝ C'.center (target v) ∧
      Disjoint (closure C'.disk) K ∧
      (∀ w∈B, ∀ z∈E'.region w, z∈K → z∈E.region w) := by
  obtain ⟨n,P,hP⟩ := (E.joined v hv).exists_simple_segmentChain
  cases n with
  | zero =>
    have he : C.drawing.point v=target v := P.start.symm.trans P.finish
    exact False.elim (Set.disjoint_left.mp hCK (he ▸ C.point_mem v) htK)
  | succ n =>
    obtain ⟨C₁,E₁,P₁,hP₁,hr₁,hC₁,hprotect₁⟩ := C.align E hleaf hv hK hCK P hP
    have hE₁ : ∀ z∈E₁.region v, z∈K → z=target v := fun z hz hzK =>
      hEK z (hprotect₁ v hv z hz hzK) hzK
    obtain ⟨C₂,E₂,hseg₂,hr₂,hC₂,hprotect₂⟩ := C₁.prepare_radial E₁ hleaf hv hK hC₁ hE₁ P₁ hP₁ hr₁
    exact ⟨C₂,E₂,hseg₂,hr₂,hC₂,fun w hw z hz hzK =>
      hprotect₁ w hw z (hprotect₂ w hw z hz hzK) hzK⟩

end DiskCore
end PlanarL1.Topology



end

end OAI
