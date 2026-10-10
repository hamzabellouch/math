import OAI.Combinatorics.PlanarL1.TreeDisk

namespace OAI

section



namespace PlanarL1.Topology
open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma small_homothety_subset {S U : Set E} (hS : Bornology.IsBounded S)
    (hU : U ∈ nhds (0:E)) :
    ∃ c : ℝ, 0<c ∧ c<1 ∧ (fun x : E => c•x) '' S ⊆ U := by
  obtain ⟨R,hR,hbound⟩ := hS.exists_pos_norm_le
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  let c := min (1/2:ℝ) (ε/(2*R))
  have hc : 0<c := lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hR))
  have hc1 : c<1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨c,hc,hc1,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  apply hball
  rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  have hcr : c*R ≤ ε/2 := by
    calc c*R ≤ (ε/(2*R))*R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
         _ = ε/2 := by field_simp
  calc c*‖x‖ ≤ c*R := mul_le_mul_of_nonneg_left (hbound x hx) hc.le
       _ ≤ ε/2 := hcr
       _ < ε := by linarith

/-- The radial exit from a convex neighbourhood. Both portions of the original
segment are controlled; this is the actual cut used in a disk surgery. -/
lemma convex_radial_cut {S : Set E} (hS : Convex ℝ S) (h0 : S ∈ nhds (0:E))
    {p : E} (hp : p ∉ closure S) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ t•p ∈ frontier S ∧
      (∀ s : ℝ, 0 ≤ s → s < t → s • p ∈ interior S) ∧
      (∀ s : ℝ, t < s → s • p ∉ closure S) := by
  have hg : 1<gauge S p := lt_of_not_ge (fun h => hp ((gauge_le_one_iff_mem_closure hS h0).mp h))
  let t := (gauge S p)⁻¹
  have ht : 0<t := inv_pos.mpr (lt_trans zero_lt_one hg)
  have ht1 : t<1 := (inv_lt_one₀ (lt_trans zero_lt_one hg)).mpr hg
  have he : t*gauge S p=1 := inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one hg))
  refine ⟨t,ht,ht1,?_,?_,?_⟩
  · apply (gauge_eq_one_iff_mem_frontier hS h0).mp
    simpa only [gauge_smul_of_nonneg ht.le,smul_eq_mul] using he
  · intro s hs hst
    apply (gauge_lt_one_iff_mem_interior hS h0).mp
    rw [gauge_smul_of_nonneg hs,smul_eq_mul,← he]
    exact mul_lt_mul_of_pos_right hst (lt_trans zero_lt_one hg)
  · intro s hst hs
    have hs0 : 0 ≤ s := le_of_lt (lt_trans ht hst)
    have hs' := (gauge_le_one_iff_mem_closure hS h0).mpr hs
    rw [gauge_smul_of_nonneg hs0,smul_eq_mul,← he] at hs'
    exact (mul_lt_mul_of_pos_right hst (lt_trans zero_lt_one hg)).not_ge hs'

lemma convex_frontier_radial_interior {S : Set E} (hS : Convex ℝ S)
    (h0 : S ∈ nhds (0:E)) {p : E} (hp : p ∈ frontier S)
    {t : ℝ} (ht : 0≤t) (ht1 : t<1) : t•p ∈ interior S := by
  apply (gauge_lt_one_iff_mem_interior hS h0).mp
  rw [gauge_smul_of_nonneg ht,(gauge_eq_one_iff_mem_frontier hS h0).mpr hp]
  simpa only [smul_eq_mul,mul_one] using ht1

lemma convex_frontier_scaled_segment {S : Set E} (hS : Convex ℝ S)
    (h0 : S ∈ nhds (0:E)) {p : E} (hp : p ∈ frontier S)
    {c t : ℝ} (hc : 0≤c) (hct : c≤t) (ht : t≤1) :
    segment ℝ (c•p) (t•p) ⊆ closure S := by
  apply hS.closure.segment_subset
  · apply (gauge_le_one_iff_mem_closure hS h0).mp
    rw [gauge_smul_of_nonneg hc,(gauge_eq_one_iff_mem_frontier hS h0).mpr hp]
    simpa only [smul_eq_mul,mul_one] using hct.trans ht
  · apply (gauge_le_one_iff_mem_closure hS h0).mp
    rw [gauge_smul_of_nonneg (hc.trans hct),(gauge_eq_one_iff_mem_frontier hS h0).mpr hp]
    simpa only [smul_eq_mul,mul_one] using ht

end PlanarL1.Topology

namespace PlanarL1.Topology.PLDrawing
open Set Metric Filter
variable {V : Type} [LinearOrder V] {G : SimpleGraph V}

/-- Polygonal edge regions with exactly the prescribed intersections give a
literal simple polyline drawing, by finite loop erasure inside each region. -/
lemma ofRegions (p : V → ℂ) (hp : Function.Injective p)
    (R : ForwardDart G → Set ℂ)
    (hmem : ∀ d, p d.val.fst ∈ R d)
    (hjoin : ∀ d, PolygonallyJoined (R d) (p d.val.fst) (p d.val.snd))
    (hvertex : ∀ d v, p v ∈ R d → Incident d v)
    (hinter : ∀ d e, d≠e → ∀ z, z∈R d → z∈R e →
      (z=p d.val.fst ∨ z=p d.val.snd) ∧ (z=p e.val.fst ∨ z=p e.val.snd)) :
    ∃ Q : PLDrawing G, Q.point=p ∧ ∀ d, (Q.chain d).trace ⊆ R d := by
  classical
  choose n C hC using fun d => (hjoin d).exists_simple_segmentChain
  refine ⟨⟨p,hp,n,fun d => (C d).mapSet (Set.subset_univ _),
    fun d => (C d).mapSet_simple _ (hC d),?_,?_⟩,rfl,?_⟩
  · intro d v hv
    exact hvertex d v ((C d).trace_subset (hmem d) hv)
  · intro d e hde z hz hz'
    exact hinter d e hde z ((C d).trace_subset (hmem d) hz)
      ((C e).trace_subset (hmem e) hz')
  · intro d
    exact (C d).trace_subset (hmem d)

variable (P : PLDrawing G)

noncomputable def radialPoint (B : Set V) (c : ℝ) (t : V → ℝ) (v : V) : ℂ :=
  by classical exact if v∈B then t v • P.point v else c • P.point v

def radialRegion (B : Set V) (c : ℝ) (t : V → ℝ) (d : ForwardDart G) : Set ℂ :=
  (fun z : ℂ => c•z) '' (P.chain d).trace ∪
    ⋃ v : {v : V // v∈B ∧ Incident d v}, segment ℝ (c•P.point v.val) (t v.val•P.point v.val)

variable {S : Set ℂ} (hS : Convex ℝ S) (h0 : S ∈ nhds (0:ℂ))
  (hpoint : ∀ v, P.point v ∈ closure S)
  {B : Set V} (hport : ∀ v ∈ B, P.point v ∈ frontier S)
  {c : ℝ} (hc : 0<c) (hc1 : c<1) {t : V → ℝ}
  (ht : ∀ v∈B, c<t v ∧ t v≤1)

include hc hc1 ht
omit hc in
lemma radial_segment_subset {v : V} (hv : v∈B) :
    segment ℝ (c•P.point v) (t v•P.point v) ⊆ P.portTail c v := by
  change segment ℝ (c•P.point v) (t v•P.point v) ⊆ segment ℝ (c•P.point v) (P.point v)
  apply (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
  rw [segment_eq_image' ℝ]
  refine ⟨(t v-c)/(1-c),⟨div_nonneg (sub_nonneg.mpr (ht v hv).1.le) (sub_nonneg.mpr hc1.le),?_⟩,?_⟩
  · exact (div_le_one (sub_pos.mpr hc1)).mpr (by linarith [(ht v hv).2])
  · dsimp only
    have he : c+(t v-c)/(1-c)*(1-c)=t v := by field_simp [ne_of_gt (sub_pos.mpr hc1)]; ring
    calc c•P.point v+((t v-c)/(1-c))•(P.point v-c•P.point v)
          = (c+(t v-c)/(1-c)*(1-c))•P.point v := by module
         _ = t v•P.point v := by rw [he]

omit hc in
lemma radialRegion_subset (d : ForwardDart G) :
    P.radialRegion B c t d ⊆ P.expandedRegion B c d := by
  rintro z (hz | hz)
  · exact Or.inl hz
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    exact Or.inr (Set.mem_iUnion.mpr ⟨v,P.radial_segment_subset hc1 ht v.property.1 hv⟩)

include hS h0 hport
omit hc1 in
lemma radial_port_not_core {v : V} (hv : v∈B) :
    t v•P.point v ∉ (fun z : ℂ => c•z) '' closure S := by
  rintro ⟨z,hz,he⟩
  have hg := congrArg (gauge S) he
  rw [gauge_smul_of_nonneg hc.le,gauge_smul_of_nonneg (hc.le.trans (ht v hv).1.le),
    (gauge_eq_one_iff_mem_frontier hS h0).mpr (hport v hv)] at hg
  have hz' := (gauge_le_one_iff_mem_closure hS h0).mpr hz
  simp only [smul_eq_mul,mul_one] at hg
  nlinarith [(ht v hv).1]

include hpoint
omit hc1 in
lemma radialPoint_injective : Function.Injective (P.radialPoint B c t) := by
  classical
  intro v w he
  by_cases hv : v∈B <;> by_cases hw : w∈B
  · apply P.point_injective
    exact (convex_frontier_radial_injective hS h0 (hport v hv) (hport w hw)
      (hc.trans (ht v hv).1) (hc.trans (ht w hw).1)
      (by simpa only [radialPoint,ite_eq_left hv,ite_eq_left hw] using he)).2
  · exfalso
    apply P.radial_port_not_core hS h0 hport hc ht hv
    exact ⟨P.point w,hpoint w,by simpa only [radialPoint,ite_eq_left hv,ite_eq_right hw] using he.symm⟩
  · exfalso
    apply P.radial_port_not_core hS h0 hport hc ht hw
    exact ⟨P.point v,hpoint v,by simpa only [radialPoint,ite_eq_right hv,ite_eq_left hw] using he⟩
  · apply P.point_injective
    exact smul_right_injective ℂ hc.ne' (by simpa only [radialPoint,ite_eq_right hv,ite_eq_right hw] using he)

lemma radialPoint_in_tail {v w : V} (hw : w∈B)
    (h : P.radialPoint B c t v ∈ P.portTail c w) : v=w := by
  classical
  by_cases hv : v∈B
  · by_contra hne
    have hd := convex_frontier_tails_disjoint hS h0 (hport v hv) (hport w hw)
      (fun h => hne (P.point_injective h)) hc hc1.le
    exact Set.disjoint_left.mp hd
      (P.radial_segment_subset hc1 ht hv (right_mem_segment ℝ _ _))
      (by simpa only [radialPoint,ite_eq_left hv,portTail] using h)
  · apply P.point_injective
    apply smul_right_injective ℂ hc.ne'
    exact convex_frontier_tail_core hS h0 (hport w hw) hc hc1.le
      (by simpa only [radialPoint,ite_eq_right hv,portTail] using h) ⟨P.point v,hpoint v,rfl⟩

variable (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
include htrace
lemma radialRegion_vertex {d : ForwardDart G} {v : V}
    (hv : P.radialPoint B c t v ∈ P.radialRegion B c t d) : Incident d v := by
  classical
  rcases hv with hv | hv
  · have hvB : v∉B := by
      intro hvB
      apply P.radial_port_not_core hS h0 hport hc ht hvB
      simpa only [radialPoint,ite_eq_left hvB] using Set.image_mono (htrace d) hv
    obtain ⟨z,hz,he⟩ := hv
    have he' : z=P.point v := smul_right_injective ℂ hc.ne'
      (by simpa only [radialPoint,ite_eq_right hvB] using he)
    exact P.on_vertex d v (he' ▸ hz)
  · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hv
    have he := P.radialPoint_in_tail hS h0 hpoint hport hc hc1 ht w.property.1
      (P.radial_segment_subset hc1 ht w.property.1 hw)
    exact he ▸ w.property.2


variable (hleaf : ∀ v ∈ B, ∀ a b, G.Adj v a → G.Adj v b → a=b)
include hleaf
lemma radialRegions_intersect {d e : ForwardDart G} (hde : d≠e)
    {z : ℂ} (hz : z∈P.radialRegion B c t d) (hz' : z∈P.radialRegion B c t e) :
    (z=P.radialPoint B c t d.val.fst ∨ z=P.radialPoint B c t d.val.snd) ∧
    (z=P.radialPoint B c t e.val.fst ∨ z=P.radialPoint B c t e.val.snd) := by
  classical
  have hd := P.radialRegion_subset hc1 ht d hz
  have he := P.radialRegion_subset hc1 ht e hz'
  have hint := P.expandedRegions_intersect hS h0 hport hc hc1 htrace hleaf hde hd he
  have hnot (v : V) (hv : z=P.expandedPoint B c v) : v∉B := by
    intro hvB
    exact hde (leaf_incident_unique hleaf hvB
      (P.expandedRegion_vertex hS h0 hpoint hport hc hc1 (htrace d) (hv ▸ hd))
      (P.expandedRegion_vertex hS h0 hpoint hport hc hc1 (htrace e) (hv ▸ he)))
  have heq (v : V) (hv : z=P.expandedPoint B c v) : z=P.radialPoint B c t v := by
    simpa only [expandedPoint,radialPoint,ite_eq_right (hnot v hv)] using hv
  exact ⟨hint.1.imp (heq _) (heq _),hint.2.imp (heq _) (heq _)⟩

omit hS h0 hpoint hport hc hc1 ht htrace hleaf in
lemma radialPoint_mem_region {d : ForwardDart G} {v : V} (hv : Incident d v) :
    P.radialPoint B c t v ∈ P.radialRegion B c t d := by
  classical
  by_cases hvB : v∈B
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨v,hvB,hv⟩,by
      simpa only [radialPoint,ite_eq_left hvB] using right_mem_segment ℝ (c•P.point v) (t v•P.point v)⟩)
  · apply Or.inl
    refine ⟨P.point v,?_,by simp only [radialPoint,ite_eq_right hvB]⟩
    rcases hv with rfl | rfl
    · exact (P.chain d).start_mem_trace
    · exact (P.chain d).finish_mem_trace

omit hS h0 hpoint hport hc hc1 ht htrace hleaf in
lemma radialRegion_joined (B : Set V) (c : ℝ) (t : V → ℝ) (d : ForwardDart G) :
    PolygonallyJoined (P.radialRegion B c t d)
      (P.radialPoint B c t d.val.fst) (P.radialPoint B c t d.val.snd) := by
  classical
  have hseg (v : V) (hv : Incident d v) :
      segment ℝ (c•P.point v) (P.radialPoint B c t v) ⊆ P.radialRegion B c t d := by
    by_cases hvB : v∈B
    · intro z hz
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨v,hvB,hv⟩,by simpa only [radialPoint,ite_eq_left hvB] using hz⟩)
    · simp only [radialPoint,hvB,ite_false,segment_same]
      intro z hz
      have he : z=c•P.point v := hz
      subst z
      simpa only [radialPoint,ite_eq_right hvB] using P.radialPoint_mem_region (B:=B) (c:=c) (t:=t) hv
  have hfirst : PolygonallyJoined (P.radialRegion B c t d)
      (P.radialPoint B c t d.val.fst) (c•P.point d.val.fst) :=
    Relation.ReflTransGen.single (by rw [segment_symm]; exact hseg _ (Or.inl rfl))
  have hmiddle := ((P.chain d).joined_trace.smul c).mono
    (show (fun z : ℂ => c•z) '' (P.chain d).trace ⊆ P.radialRegion B c t d from fun _ h => Or.inl h)
  exact (hfirst.trans hmiddle).tail (hseg _ (Or.inr rfl))

/-- All leaf tails may be cut at different positive radial coordinates. The
result is an actual drawing, not merely a nonintersection promise. -/
lemma radial_leaf_ports : ∃ Q : PLDrawing G,
    Q.point=P.radialPoint B c t ∧ ∀ d, (Q.chain d).trace ⊆ P.radialRegion B c t d := by
  apply ofRegions (P.radialPoint B c t) (P.radialPoint_injective hS h0 hpoint hport hc ht)
    (P.radialRegion B c t)
  · intro d
    exact P.radialPoint_mem_region (Or.inl rfl)
  · exact P.radialRegion_joined B c t
  · intro d v hv
    exact P.radialRegion_vertex hS h0 hpoint hport hc hc1 ht htrace hv
  · intro d e hde z hz hz'
    exact P.radialRegions_intersect hS h0 hpoint hport hc hc1 ht htrace hleaf hde hz hz'

omit hS h0 hpoint hport hc hc1 ht htrace hleaf in
lemma radialRegion_subset_convex {U : Set ℂ} (hU : Convex ℝ U)
    (hcore : ∀ d, (fun z : ℂ => c•z) '' (P.chain d).trace ⊆ U)
    (hnew : ∀ v∈B, t v•P.point v ∈ U) (d : ForwardDart G) :
    P.radialRegion B c t d ⊆ U := by
  rintro z (hz | hz)
  · exact hcore d hz
  · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
    apply hU.segment_subset ?_ (hnew v v.property.1) hv
    apply hcore d
    refine ⟨P.point v,?_,rfl⟩
    rcases v.property.2 with he | he
    · rw [he]; exact (P.chain d).start_mem_trace
    · rw [he]; exact (P.chain d).finish_mem_trace

end PlanarL1.Topology.PLDrawing




namespace PlanarL1.Topology
open Set Metric Filter

lemma PolygonallyJoined.symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {x y : E} (h : PolygonallyJoined S x y) : PolygonallyJoined S y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact (Relation.ReflTransGen.single (by rw [segment_symm]; exact hab)).trans ih

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

noncomputable def movedPoint (v : V) (q : ℂ) (w : V) : ℂ :=
  by classical exact if w=v then q else P.point w

def movedRegion (v : V) (S : Set ℂ) (d : ForwardDart G) : Set ℂ :=
  (P.chain d).trace ∪ {z | Incident d v ∧ z∈S}

variable {v : V} {q : ℂ} {S : Set ℂ}
  (hleaf : ∀ a b, G.Adj v a → G.Adj v b → a=b)
  (hp : P.point v∈S) (hq : q∈S)
  (hvertex : ∀ w, P.point w∈S → w=v)
  (hcross : ∀ d z, z∈(P.chain d).trace → z∈S → z=P.point v)

include hq hvertex
lemma movedPoint_injective : Function.Injective (P.movedPoint v q) := by
  classical
  intro a b he
  by_cases ha : a=v <;> by_cases hb : b=v
  · exact ha.trans hb.symm
  · exfalso
    apply hb
    apply hvertex b
    have he' : q=P.point b := by simpa only [movedPoint,ite_eq_left ha,ite_eq_right hb] using he
    exact he' ▸ hq
  · exfalso
    apply ha
    apply hvertex a
    have he' : P.point a=q := by simpa only [movedPoint,ite_eq_right ha,ite_eq_left hb] using he
    exact he'.symm ▸ hq
  · apply P.point_injective
    simpa only [movedPoint,ite_eq_right ha,ite_eq_right hb] using he

include hcross
lemma movedRegion_vertex {d : ForwardDart G} {w : V}
    (hw : P.movedPoint v q w∈P.movedRegion v S d) : Incident d w := by
  classical
  by_cases he : w=v
  · subst w
    simp only [movedPoint,ite_true,movedRegion,Set.mem_union,Set.mem_ofPred_eq] at hw
    rcases hw with hw | hw
    · have h := hcross d q hw hq
      exact P.on_vertex d v (h ▸ hw)
    · exact hw.1
  · simp only [movedPoint,ite_eq_right he,movedRegion,Set.mem_union,Set.mem_ofPred_eq] at hw
    rcases hw with hw | hw
    · exact P.on_vertex d w hw
    · exact False.elim (he (hvertex w hw.2))

include hleaf
omit hq hvertex in
lemma movedRegions_intersect {d e : ForwardDart G} (hde : d≠e) {z : ℂ}
    (hz : z∈P.movedRegion v S d) (hz' : z∈P.movedRegion v S e) :
    (z=P.movedPoint v q d.val.fst ∨ z=P.movedPoint v q d.val.snd) ∧
    (z=P.movedPoint v q e.val.fst ∨ z=P.movedPoint v q e.val.snd) := by
  classical
  have huniq : ∀ {d e : ForwardDart G}, Incident d v → Incident e v → d=e := by
    intro d e hd he
    exact leaf_incident_unique (B:={v}) (by intro w hw; have : w=v := hw; simpa [this] using hleaf)
      rfl hd he
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · have hint := P.intersect d e hde z hz hz'
    have hne (w : V) (he : z=P.point w) : w≠v := by
      intro hw
      have hev : z=P.point v := he.trans (congrArg P.point hw)
      exact hde (huniq (P.on_vertex d v (hev ▸ hz)) (P.on_vertex e v (hev ▸ hz')))
    have heq (w : V) (he : z=P.point w) : z=P.movedPoint v q w := by
      simpa only [movedPoint,ite_eq_right (hne w he)] using he
    exact ⟨hint.1.imp (heq _) (heq _),hint.2.imp (heq _) (heq _)⟩
  · have he := hcross d z hz hz'.2
    exact False.elim (hde (huniq (P.on_vertex d v (he ▸ hz)) hz'.1))
  · have he := hcross e z hz' hz.2
    exact False.elim (hde (huniq hz.1 (P.on_vertex e v (he ▸ hz'))))
  · exact False.elim (hde (huniq hz.1 hz'.1))

omit hleaf hvertex hcross in
lemma movedPoint_mem_region {d : ForwardDart G} {w : V} (hw : Incident d w) :
    P.movedPoint v q w∈P.movedRegion v S d := by
  classical
  by_cases he : w=v
  · subst w
    exact Or.inr ⟨hw,by simpa [movedPoint] using hq⟩
  · apply Or.inl
    simpa only [movedPoint,ite_eq_right he] using
      (show P.point w∈(P.chain d).trace from by
        rcases hw with rfl | rfl
        · exact (P.chain d).start_mem_trace
        · exact (P.chain d).finish_mem_trace)


omit hleaf hq hvertex hcross in
lemma movedRegion_joined (hjoin : PolygonallyJoined S (P.point v) q) (d : ForwardDart G) :
    PolygonallyJoined (P.movedRegion v S d)
      (P.movedPoint v q d.val.fst) (P.movedPoint v q d.val.snd) := by
  classical
  have hroute (w : V) (hw : Incident d w) :
      PolygonallyJoined (P.movedRegion v S d) (P.point w) (P.movedPoint v q w) := by
    by_cases he : w=v
    · subst w
      simpa [movedPoint] using hjoin.mono
        (show S ⊆ P.movedRegion v S d from fun z hz => Or.inr ⟨hw,hz⟩)
    · simp only [movedPoint,ite_eq_right he]
      exact Relation.ReflTransGen.refl
  exact ((hroute _ (Or.inl rfl)).symm.trans
    ((P.chain d).joined_trace.mono (fun _ h => Or.inl h))).trans (hroute _ (Or.inr rfl))

/-- Extending a drawn leaf along a polygonal region disjoint from the rest of
the drawing preserves a literal polyline drawing and the exact vertices. -/
lemma move_leaf (hjoin : PolygonallyJoined S (P.point v) q) :
    ∃ Q : PLDrawing G, Q.point=P.movedPoint v q ∧
      ∀ d, (Q.chain d).trace ⊆ P.movedRegion v S d := by
  apply ofRegions (P.movedPoint v q) (P.movedPoint_injective hq hvertex) (P.movedRegion v S)
  · intro d
    exact P.movedPoint_mem_region hq (Or.inl rfl)
  · exact P.movedRegion_joined hjoin
  · intro d w hw
    exact P.movedRegion_vertex hq hvertex hcross hw
  · intro d e hde z hz hz'
    exact P.movedRegions_intersect hleaf hcross hde hz hz'

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma convex_segment_cut {S : Set E} (hS : Convex ℝ S) (hopen : IsOpen S)
    {a b : E} (ha : a∈S) (hb : b∉closure S) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ a+t•(b-a)∈frontier S ∧
      (∀ s : ℝ, 0 ≤ s → s < t → a+s•(b-a)∈S) ∧
      (∀ s : ℝ, t < s → a+s•(b-a)∉closure S) := by
  let T := (fun z : E => a+z) ⁻¹' S
  have hT : Convex ℝ T := hS.translate_preimage_right a
  have hop : IsOpen T := hopen.preimage (continuous_const.add continuous_id)
  have hzero : T∈nhds (0:E) := hop.mem_nhds (by simpa [T] using ha)
  have hcl : closure T=(fun z : E => a+z) ⁻¹' closure S :=
    ((Homeomorph.addLeft a).preimage_closure S).symm
  have hfr : frontier T=(fun z : E => a+z) ⁻¹' frontier S :=
    ((Homeomorph.addLeft a).preimage_frontier S).symm
  have hb' : b-a∉closure T := by simpa [hcl] using hb
  obtain ⟨t,ht,ht1,htfr,hin,hout⟩ := convex_radial_cut hT hzero hb'
  refine ⟨t,ht,ht1,?_,?_,?_⟩
  · simpa only [hfr,Set.mem_preimage] using htfr
  · intro s hs hst
    exact (show s•(b-a)∈T from interior_subset (hin s hs hst))
  · intro s hst hs
    apply hout s hst
    simpa only [hcl,Set.mem_preimage] using hs

lemma convex_frontier_segment {S : Set E} (hS : Convex ℝ S)
    (h0 : S∈nhds (0:E)) {p q : E} (hp : p∈frontier S) (hq : q∈frontier S)
    (hseg : q∈segment ℝ 0 p) : q=p := by
  rw [segment_eq_image' ℝ 0 p] at hseg
  obtain ⟨t,ht,he⟩ := hseg
  simp only [zero_add,sub_zero] at he
  have hg := congrArg (gauge S) he
  rw [gauge_smul_of_nonneg ht.1,(gauge_eq_one_iff_mem_frontier hS h0).mpr hp,
    (gauge_eq_one_iff_mem_frontier hS h0).mpr hq] at hg
  simp only [smul_eq_mul,mul_one] at hg
  simpa only [hg,one_smul] using he.symm

/-- A convex capsule around one radial arm avoids all other ports and every
closed external obstacle. This is the merging disk, not an assumed regular
neighbourhood of an embedded tree. -/
lemma capsule_avoiding_ports {ι : Type*} [Finite ι] (p : ι → ℂ)
    (hinj : Function.Injective p) {B : Set ι} {v : ι} (hv : v∈B)
    {S F : Set ℂ} (hS : Convex ℝ S) (h0 : S∈nhds (0:ℂ))
    (hport : ∀ w∈B, p w∈frontier S) (hF : IsClosed F)
    (hdisj : Disjoint (segment ℝ 0 (p v)) F) :
    ∃ T : Set ℂ, Convex ℝ T ∧ IsOpen T ∧ Bornology.IsBounded T ∧
      segment ℝ 0 (p v) ⊆ T ∧ Disjoint (closure T) F ∧
      ∀ w∈B, w≠v → p w∉closure T := by
  let A := p '' {w | w∈B ∧ w≠v}
  have hA : IsClosed A := ((Set.toFinite _).image p).isClosed
  have hdA : Disjoint (segment ℝ 0 (p v)) A := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨w,⟨hw,hne⟩,rfl⟩
    exact hne (hinj (convex_frontier_segment hS h0 (hport v hv) (hport w hw) hz))
  obtain ⟨T,hT,hTop,hTb,hseg,hd⟩ := convex_tube_avoiding (hF.union hA)
    (hdisj.union_right hdA)
  refine ⟨T,hT,hTop,hTb,hseg,hd.mono_right Set.subset_union_left,?_⟩
  intro w hw hne hp
  exact Set.disjoint_left.mp hd hp (Or.inr ⟨w,⟨hw,hne⟩,rfl⟩)

/-- Radial cuts of all unselected ports, after a sufficiently small homothety
of the bounded old disk. The selected port stays in the interior of the new
disk; it will be extended along the next exterior straight piece. -/
lemma capsule_radial_data {ι : Type*} (p : ι → ℂ) {B : Set ι} {v : ι}
    {S T : Set ℂ} (hSbound : Bornology.IsBounded S)
    (hpoint : ∀ w, p w∈closure S)
    (hT : Convex ℝ T) (hTop : IsOpen T) (hT0 : (0:ℂ)∈T)
    (hout : ∀ w∈B, w≠v → p w∉closure T) :
    ∃ (c : ℝ) (t : ι → ℝ), 0<c ∧ c<1 ∧
      (fun z : ℂ => c•z) '' closure S ⊆ T ∧ t v=1 ∧
      (∀ w∈B, c<t w ∧ t w≤1) ∧
      (∀ w∈B, w≠v → t w•p w∈frontier T) ∧
      (∀ w∈B, w≠v → ∀ s : ℝ, t w < s → s•p w∉closure T) := by
  classical
  obtain ⟨c,hc,hc1,hcore⟩ := small_homothety_subset hSbound.closure (hTop.mem_nhds hT0)
  let W := {w : ι // w∈B ∧ w≠v}
  have hcut (w : W) := convex_radial_cut hT (hTop.mem_nhds hT0) (hout w w.property.1 w.property.2)
  choose u hu hu1 huf hin hf using hcut
  let t (w : ι) := if h : w∈B ∧ w≠v then u ⟨w,h⟩ else 1
  have hct (w : W) : c<u w := by
    have hcT : c•p w∈interior T := by rw [hTop.interior_eq]; exact hcore ⟨p w,hpoint w,rfl⟩
    have hgc := (gauge_lt_one_iff_mem_interior hT (hTop.mem_nhds hT0)).mpr hcT
    have hgu := (gauge_eq_one_iff_mem_frontier hT (hTop.mem_nhds hT0)).mpr (huf w)
    rw [gauge_smul_of_nonneg hc.le,smul_eq_mul] at hgc
    rw [gauge_smul_of_nonneg (hu w).le,smul_eq_mul] at hgu
    have hgp : 1<gauge T (p w) := lt_of_not_ge (fun h =>
      hout w w.property.1 w.property.2 ((gauge_le_one_iff_mem_closure hT (hTop.mem_nhds hT0)).mp h))
    nlinarith
  refine ⟨c,t,hc,hc1,hcore,by simp [t],?_,?_,?_⟩
  · intro w hw
    by_cases he : w=v
    · subst w; simp only [t,ne_eq,not_true_eq_false,and_false,dite_false]; exact ⟨hc1,le_rfl⟩
    · have hwv : w∈B ∧ w≠v := ⟨hw,he⟩
      simpa only [t,dite_eq_left hwv] using
        (show c<u ⟨w,hwv⟩ ∧ u ⟨w,hwv⟩ ≤ 1 from ⟨hct ⟨w,hwv⟩,(hu1 ⟨w,hwv⟩).le⟩)
  · intro w hw he
    have hwv : w∈B ∧ w≠v := ⟨hw,he⟩
    simpa only [t,dite_eq_left hwv] using huf ⟨w,hwv⟩
  · intro w hw he s hs
    have hwv : w∈B ∧ w≠v := ⟨hw,he⟩
    exact hf ⟨w,hwv⟩ s (by simpa only [t,dite_eq_left hwv] using hs)

end PlanarL1.Topology




namespace PlanarL1.Topology
open Set

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

noncomputable def forward (u v : V) (h : G.Adj u v) : ForwardDart G := by
  classical
  exact if huv : u<v then ⟨⟨(u,v),h⟩,huv⟩ else
    ⟨⟨(v,u),h.symm⟩,lt_of_le_of_ne (le_of_not_gt huv) (Ne.symm h.ne)⟩

lemma forward_endpoints (u v : V) (h : G.Adj u v) :
    ((forward u v h).val.fst=u ∧ (forward u v h).val.snd=v) ∨
    ((forward u v h).val.fst=v ∧ (forward u v h).val.snd=u) := by
  classical
  by_cases huv : u<v <;> simp [forward,huv]

lemma forward_symm (u v : V) (h : G.Adj u v) : forward u v h=forward v u h.symm := by
  apply ForwardDart.eq_of_endpoints
  rcases forward_endpoints u v h with h₁|h₁ <;>
    rcases forward_endpoints v u h.symm with h₂|h₂
  · exact Or.inr ⟨h₁.1.trans h₂.2.symm,h₁.2.trans h₂.1.symm⟩
  · exact Or.inl ⟨h₁.1.trans h₂.1.symm,h₁.2.trans h₂.2.symm⟩
  · exact Or.inl ⟨h₁.1.trans h₂.1.symm,h₁.2.trans h₂.2.symm⟩
  · exact Or.inr ⟨h₁.1.trans h₂.2.symm,h₁.2.trans h₂.1.symm⟩

noncomputable def region (u v : V) : Set ℂ := by
  classical exact if h : G.Adj u v then (P.chain (forward u v h)).trace else ∅

lemma region_eq (u v : V) (h : G.Adj u v) :
    P.region u v=(P.chain (forward u v h)).trace := by simp [region,h]

lemma region_symm (u v : V) : P.region u v=P.region v u := by
  classical
  by_cases h : G.Adj u v
  · rw [P.region_eq u v h,P.region_eq v u h.symm,forward_symm]
  · simp [region,h,show ¬G.Adj v u from fun h' => h h'.symm]

lemma region_joined (u v : V) (h : G.Adj u v) :
    PolygonallyJoined (P.region u v) (P.point u) (P.point v) := by
  rw [P.region_eq u v h]
  rcases forward_endpoints u v h with he|he
  · simpa only [he.1,he.2] using (P.chain (forward u v h)).joined_trace
  · simpa only [he.1,he.2] using (P.chain (forward u v h)).joined_trace.symm

lemma region_start (u v : V) (h : G.Adj u v) : P.point u∈P.region u v := by
  rw [P.region_eq u v h]
  rcases forward_endpoints u v h with he|he
  · simpa only [(P.chain (forward u v h)).start,he.1] using (P.chain (forward u v h)).vertex_mem_trace 0 (Nat.zero_le _)
  · have hmem := (P.chain (forward u v h)).vertex_mem_trace (P.count (forward u v h)) le_rfl
    simpa only [(P.chain (forward u v h)).finish,he.2] using hmem

lemma region_end (u v : V) (h : G.Adj u v) : P.point v∈P.region u v := by
  rw [P.region_symm]; exact P.region_start v u h.symm

lemma region_vertex (u v : V) (h : G.Adj u v) (w : V) (hw : P.point w∈P.region u v) :
    w=u ∨ w=v := by
  rw [P.region_eq u v h] at hw
  have hh := P.on_vertex _ w hw
  rcases forward_endpoints u v h with he|he
  · simpa only [he.1,he.2] using hh
  · simpa only [he.1,he.2,or_comm] using hh

lemma region_intersect (u v w x : V) (huv : G.Adj u v) (hwx : G.Adj w x)
    (hne : ¬((u=w ∧ v=x) ∨ (u=x ∧ v=w))) {z : ℂ}
    (hz : z∈P.region u v) (hz' : z∈P.region w x) :
    (z=P.point u ∨ z=P.point v) ∧ (z=P.point w ∨ z=P.point x) := by
  rw [P.region_eq u v huv] at hz
  rw [P.region_eq w x hwx] at hz'
  have hfe : forward u v huv≠forward w x hwx := by
    intro he
    have h₁ := forward_endpoints u v huv
    rw [he] at h₁
    rcases h₁ with h₁|h₁ <;> rcases forward_endpoints w x hwx with h₂|h₂
    · exact hne (Or.inl ⟨h₁.1.symm.trans h₂.1,h₁.2.symm.trans h₂.2⟩)
    · exact hne (Or.inr ⟨h₁.1.symm.trans h₂.1,h₁.2.symm.trans h₂.2⟩)
    · exact hne (Or.inr ⟨h₁.2.symm.trans h₂.2,h₁.1.symm.trans h₂.1⟩)
    · exact hne (Or.inl ⟨h₁.2.symm.trans h₂.2,h₁.1.symm.trans h₂.1⟩)
  have hi := P.intersect _ _ hfe z hz hz'
  rcases forward_endpoints u v huv with h₁|h₁ <;>
    rcases forward_endpoints w x hwx with h₂|h₂ <;>
    simpa only [h₁.1,h₁.2,h₂.1,h₂.2,or_comm] using hi

lemma ofSymmetricRegions (p : V → ℂ) (hp : Function.Injective p)
    (R : V → V → Set ℂ)
    (hmem : ∀ u v, G.Adj u v → p u∈R u v)
    (hjoin : ∀ u v, G.Adj u v → PolygonallyJoined (R u v) (p u) (p v))
    (hvertex : ∀ u v, G.Adj u v → ∀ w, p w∈R u v → w=u ∨ w=v)
    (hinter : ∀ u v w x, G.Adj u v → G.Adj w x →
      ¬((u=w ∧ v=x) ∨ (u=x ∧ v=w)) → ∀ z, z∈R u v → z∈R w x →
      (z=p u ∨ z=p v) ∧ (z=p w ∨ z=p x)) :
    ∃ Q : PLDrawing G, Q.point=p ∧ ∀ d, (Q.chain d).trace ⊆ R d.val.fst d.val.snd := by
  apply ofRegions p hp (fun d => R d.val.fst d.val.snd)
  · intro d; exact hmem _ _ d.val.adj
  · intro d; exact hjoin _ _ d.val.adj
  · intro d w hw; exact hvertex _ _ d.val.adj w hw
  · intro d e hde z hz hz'
    exact hinter _ _ _ _ d.val.adj e.val.adj
      (fun he => hde (ForwardDart.eq_of_endpoints d e he)) z hz hz'

end PLDrawing

/-- Adding finitely many new leaves to one vertex; no geometric or metric
conclusion is included in this graph definition. -/
def leafExtension {V W : Type} (G : SimpleGraph V) (v : V) : SimpleGraph (V⊕W) where
  Adj x y := match x,y with
    | .inl a,.inl b => G.Adj a b
    | .inl a,.inr _ => a=v
    | .inr _,.inl a => a=v
    | .inr _,.inr _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> dsimp at h ⊢
    all_goals first | exact h | exact h.symm⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

namespace PLDrawing
variable {V W : Type} [LinearOrder V] [LinearOrder W] [LinearOrder (V⊕W)] {G : SimpleGraph V}
variable (P : PLDrawing G) (v : V) (q : W → ℂ) (A : W → Set ℂ)

def starPoint : V⊕W → ℂ := Sum.elim P.point q

def starRegion : V⊕W → V⊕W → Set ℂ
  | .inl a,.inl b => P.region a b
  | .inl _,.inr w => A w
  | .inr w,.inl _ => A w
  | .inr _,.inr _ => ∅

/-- A finite star of genuinely disjoint polygonal arms can be attached at an
existing vertex while retaining every old vertex and edge region. -/
lemma attachLeaves
    (hq : ∀ w, q w≠P.point v)
    (hstart : ∀ w, P.point v∈A w) (hend : ∀ w, q w∈A w)
    (hjoin : ∀ w, PolygonallyJoined (A w) (P.point v) (q w))
    (hvertex : ∀ w u, P.point u∈A w → u=v)
    (hdisj : ∀ w w', w≠w' → ∀ z, z∈A w → z∈A w' → z=P.point v)
    (hold : ∀ w u x, G.Adj u x → ∀ z, z∈A w → z∈P.region u x → z=P.point v) :
    ∃ Q : PLDrawing (leafExtension (W := W) G v), Q.point=P.starPoint q ∧
      ∀ d, (Q.chain d).trace ⊆ P.starRegion A d.val.fst d.val.snd := by
  have hqold (w : W) (u : V) : q w≠P.point u := by
    intro he
    have hue : u=v := hvertex w u (he ▸ hend w)
    exact hq w (he.trans (congrArg P.point hue))
  have hqq : Function.Injective q := by
    intro w w' he
    by_contra hn
    exact hq w (hdisj w w' hn (q w) (hend w) (he ▸ hend w'))
  have hp : Function.Injective (P.starPoint q) := by
    intro x y he
    cases x with
    | inl x => cases y with
      | inl y => exact congrArg Sum.inl (P.point_injective he)
      | inr y => exact False.elim (hqold y x he.symm)
    | inr x => cases y with
      | inl y => exact False.elim (hqold x y he)
      | inr y => exact congrArg Sum.inr (hqq he)
  apply ofSymmetricRegions (P.starPoint q) hp (P.starRegion A)
  · intro x y hxy
    cases x with
    | inl x => cases y with
      | inl y => exact P.region_start x y hxy
      | inr y => have he : x=v := hxy; subst x; exact hstart y
    | inr x => cases y with
      | inl y => exact hend x
      | inr y => exact False.elim hxy
  · intro x y hxy
    cases x with
    | inl x => cases y with
      | inl y => exact P.region_joined x y hxy
      | inr y => have he : x=v := hxy; subst x; exact hjoin y
    | inr x => cases y with
      | inl y => have he : y=v := hxy; subst y; exact (hjoin x).symm
      | inr y => exact False.elim hxy
  · intro x y hxy z hz
    cases x with
    | inl x => cases y with
      | inl y =>
        cases z with
        | inl z => exact (P.region_vertex x y hxy z hz).imp (congrArg Sum.inl) (congrArg Sum.inl)
        | inr z =>
          exact False.elim (hq z (hold z x y hxy (q z) (hend z) hz))
      | inr y =>
        have he : x=v := hxy
        cases z with
        | inl z => exact Or.inl (congrArg Sum.inl ((hvertex y z hz).trans he.symm))
        | inr z =>
          by_cases hez : z=y
          · exact Or.inr (congrArg Sum.inr hez)
          · exact False.elim (hq z (hdisj z y hez (q z) (hend z) hz))
    | inr x => cases y with
      | inl y =>
        have he : y=v := hxy
        cases z with
        | inl z => exact Or.inr (congrArg Sum.inl ((hvertex x z hz).trans he.symm))
        | inr z =>
          by_cases hez : z=x
          · exact Or.inl (congrArg Sum.inr hez)
          · exact False.elim (hq z (hdisj z x hez (q z) (hend z) hz))
      | inr y => exact False.elim hxy
  · intro x y z t hxy hzt hne a ha hb
    cases x <;> cases y <;> cases z <;> cases t <;>
      simp only [leafExtension] at hxy hzt <;> try contradiction
    case inl.inl.inl.inl x y z t =>
      exact P.region_intersect x y z t hxy hzt (by simpa using hne) ha hb
    case inl.inl.inl.inr x y z t =>
      subst z
      have he := hold t x y hxy a hb ha
      subst a
      exact ⟨(P.region_vertex x y hxy v ha).imp (congrArg P.point) (congrArg P.point),Or.inl rfl⟩
    case inl.inl.inr.inl x y z t =>
      subst t
      have he := hold z x y hxy a hb ha
      subst a
      exact ⟨(P.region_vertex x y hxy v ha).imp (congrArg P.point) (congrArg P.point),Or.inr rfl⟩
    case inl.inr.inl.inl x y z t =>
      subst x
      have he := hold y z t hzt a ha hb
      subst a
      exact ⟨Or.inl rfl,(P.region_vertex z t hzt v hb).imp (congrArg P.point) (congrArg P.point)⟩
    case inr.inl.inl.inl x y z t =>
      subst y
      have he := hold x z t hzt a ha hb
      subst a
      exact ⟨Or.inr rfl,(P.region_vertex z t hzt v hb).imp (congrArg P.point) (congrArg P.point)⟩
    case inl.inr.inl.inr x y z t =>
      subst x; subst z
      have hyt : y≠t := by intro he; subst t; exact hne (Or.inl ⟨rfl,rfl⟩)
      rw [hdisj y t hyt a ha hb]
      exact ⟨Or.inl rfl,Or.inl rfl⟩
    case inl.inr.inr.inl x y z t =>
      subst x; subst t
      have hyz : y≠z := by intro he; subst z; exact hne (Or.inr ⟨rfl,rfl⟩)
      rw [hdisj y z hyz a ha hb]
      exact ⟨Or.inl rfl,Or.inr rfl⟩
    case inr.inl.inl.inr x y z t =>
      subst y; subst z
      have hxt : x≠t := by intro he; subst t; exact hne (Or.inr ⟨rfl,rfl⟩)
      rw [hdisj x t hxt a ha hb]
      exact ⟨Or.inr rfl,Or.inl rfl⟩
    case inr.inl.inr.inl x y z t =>
      subst y; subst t
      have hxz : x≠z := by intro he; subst z; exact hne (Or.inl ⟨rfl,rfl⟩)
      rw [hdisj x z hxz a ha hb]
      exact ⟨Or.inr rfl,Or.inr rfl⟩

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma PolygonallyJoined.affine {S : Set E} {x y : E}
    (h : PolygonallyJoined S x y) (f : E →ᵃ[ℝ] F) :
    PolygonallyJoined (f '' S) (f x) (f y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hab ih =>
    refine ih.tail ?_
    rw [← image_segment]
    exact Set.image_mono hab

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

noncomputable def affine (f : E →ᵃ[ℝ] F) : SegmentChain (f '' S) (f x) (f y) n where
  vertex i := f (P.vertex i)
  start := congrArg f P.start
  finish := congrArg f P.finish
  segment_mem i hi := by rw [← image_segment]; exact Set.image_mono (P.segment_mem i hi)

lemma affine_trace (f : E →ᵃ[ℝ] F) : (P.affine f).trace=f '' P.trace := by
  simp only [trace,affine,Set.image_union,Set.image_singleton,Set.image_iUnion,image_segment]

lemma trace_compact : IsCompact P.trace := by
  apply isCompact_singleton.union
  apply isCompact_iUnion
  intro i
  rw [segment_eq_image' ℝ]
  exact isCompact_Icc.image (by fun_prop)

lemma affine_simple (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (hP : P.IsSimple) :
    (P.affine f).IsSimple := by
  constructor
  · intro i hi j hj he; exact hP.1 hi hj (hf he)
  · intro i j hij hjn z hz hz'
    change z ∈ segment ℝ (f (P.vertex i)) (f (P.vertex (i+1))) at hz
    change z ∈ segment ℝ (f (P.vertex j)) (f (P.vertex (j+1))) at hz'
    rw [← image_segment] at hz hz'
    obtain ⟨w,hw,rfl⟩ := hz
    obtain ⟨w',hw',he⟩ := hz'
    have hwe : w'=w := hf he
    subst w'
    obtain ⟨hij',hw⟩ := hP.2 i j hij hjn w hw hw'
    exact ⟨hij',congrArg f hw⟩

noncomputable def reverse : SegmentChain S y x n where
  vertex i := P.vertex (n-i)
  start := by simpa using P.finish
  finish := by simpa using P.start
  segment_mem i hi := by
    have he : n-i=(n-(i+1))+1 := by omega
    rw [he,segment_symm]
    exact P.segment_mem (n-(i+1)) (by omega)

lemma reverse_trace : P.reverse.trace=P.trace := by
  apply Set.Subset.antisymm
  · rintro z (hz|hz)
    · have he : z=y := hz; subst z; exact P.finish_mem_trace
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      let j : Fin n := ⟨n-(i+1),by omega⟩
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨j,?_⟩
      change z∈segment ℝ (P.vertex _) (P.vertex _) at hi ⊢
      have he : n-i=(n-(i+1))+1 := by omega
      simpa only [he,segment_symm] using hi
  · rintro z (hz|hz)
    · have he : z=x := hz; subst z; exact P.reverse.finish_mem_trace
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      let j : Fin n := ⟨n-(i+1),by omega⟩
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨j,?_⟩
      change z∈segment ℝ (P.vertex _) (P.vertex _) at hi ⊢
      have h₁ : n-j=i+1 := by dsimp [j]; omega
      have h₂ : n-(j+1)=i := by dsimp [j]; omega
      simpa only [h₁,h₂,segment_symm] using hi

noncomputable def prepend (z : E) (h : segment ℝ z x ⊆ S) : SegmentChain S z y (n+1) where
  vertex i := if i=0 then z else P.vertex (i-1)
  start := by simp
  finish := by simpa using P.finish
  segment_mem i hi := by
    by_cases he : i=0
    · subst i; simpa [P.start] using h
    · simp only [ite_eq_right he,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
      have he' : i=(i-1)+1 := by omega
      conv_lhs => rhs; rw [he']
      exact P.segment_mem (i-1) (by omega)

lemma prepend_trace (z : E) (h : segment ℝ z x ⊆ S) :
    (P.prepend z h).trace=segment ℝ z x ∪ P.trace := by
  apply Set.Subset.antisymm
  · rintro w (hw|hw)
    · have he : w=z := hw; subst w; exact Or.inl (left_mem_segment ℝ _ _)
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hw
      by_cases he : (i:ℕ)=0
      · left; simpa only [prepend,he,ite_true,Nat.zero_add,one_ne_zero,ite_false,Nat.sub_self,P.start] using hi
      · right; apply Or.inr; apply Set.mem_iUnion.mpr
        refine ⟨⟨i-1,by omega⟩,?_⟩
        simpa only [prepend,ite_eq_right he,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,
          show (i:ℕ)-1+1=i by omega] using hi
  · rintro w (hw|hw)
    · apply Or.inr; apply Set.mem_iUnion.mpr
      exact ⟨⟨0,by omega⟩,by simpa [prepend,P.start] using hw⟩
    · rcases hw with hw|hw
      · have he : w=x := hw; subst w
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨0,by omega⟩,by simpa [prepend,P.start] using right_mem_segment ℝ z x⟩)
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hw
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i+1,by omega⟩,by simpa [prepend] using hi⟩)

end SegmentChain

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

noncomputable def affine (f : ℂ ≃ᵃ[ℝ] ℂ) : PLDrawing G where
  point v := f (P.point v)
  point_injective := f.injective.comp P.point_injective
  count := P.count
  chain d := ((P.chain d).affine f.toAffineMap).mapSet (Set.subset_univ _)
  simple d := ((P.chain d).affine_simple f.toAffineMap f.injective (P.simple d))
  on_vertex d v hv := by
    change f (P.point v) ∈ ((P.chain d).affine f.toAffineMap).trace at hv
    rw [(P.chain d).affine_trace f.toAffineMap] at hv
    obtain ⟨w,hw,he⟩ := hv
    have he' : w=P.point v := f.injective he
    exact P.on_vertex d v (he' ▸ hw)
  intersect d e hde z hz hz' := by
    change z ∈ ((P.chain d).affine f.toAffineMap).trace at hz
    change z ∈ ((P.chain e).affine f.toAffineMap).trace at hz'
    rw [(P.chain d).affine_trace f.toAffineMap] at hz
    rw [(P.chain e).affine_trace f.toAffineMap] at hz'
    obtain ⟨w,hw,rfl⟩ := hz
    obtain ⟨w',hw',he⟩ := hz'
    have he' : w'=w := f.injective he
    subst w'
    have hi := P.intersect d e hde w hw hw'
    exact ⟨hi.1.imp (congrArg f) (congrArg f),hi.2.imp (congrArg f) (congrArg f)⟩

lemma affine_point (f : ℂ ≃ᵃ[ℝ] ℂ) (v : V) : (P.affine f).point v=f (P.point v) := rfl
lemma affine_trace (f : ℂ ≃ᵃ[ℝ] ℂ) (d : ForwardDart G) :
    ((P.affine f).chain d).trace=f '' (P.chain d).trace := by
  exact (P.chain d).affine_trace f.toAffineMap

lemma region_compact (u v : V) : IsCompact (P.region u v) := by
  classical
  by_cases h : G.Adj u v
  · rw [P.region_eq u v h]; exact (P.chain _).trace_compact
  · simp only [region,dite_eq_right h]; exact isCompact_empty

end PLDrawing
end PlanarL1.Topology



end

end OAI
