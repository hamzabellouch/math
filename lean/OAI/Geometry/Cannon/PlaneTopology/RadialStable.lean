import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.CrosscutIncidenceLocal
import OAI.Geometry.Cannon.PlaneTopology.TameInitialInterval
import OAI.Geometry.Cannon.PlanarGraphs.IncidentSubsetPatch

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

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

variable {D : Type*} [TopologicalSpace D] [DiscreteTopology D]

theorem slit_discrete_labels_constant (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (ha₀ : a 0∈U) (hUa : a '' Ioo (0:I) 1⊆U) (ha₁ : a 1∉U)
    {π : (U\range a : Set ℂ) → D} (hπ : Continuous π) :
    ∃ d : D, ∀ z, π z=d := by
  obtain ⟨W,hW,h₀W,hWU,hWconn⟩ := tame_tip_connected_neighborhood a Q ha hU ha₀
  have hSV : W\range a⊆U\range a := sdiff_subset_sdiff_left hWU
  obtain ⟨d,hd⟩ := label_on_connected hπ hWconn hSV
  have hb (x : ℂ) (hx : x∈W) : incident (U\range a) π x⊆{d} := by
    apply incident_subset_of_patch hW _ hx
    intro y hy
    exact hd ⟨hy.1,hy.2.2⟩
  obtain ⟨l,hl⟩ := crosscut_incident_labels a Q ha hU hUa hπ
  have h₀cl : (0:I)∈closure (Ioo (0:I) 1) := by
    rw [closure_Ioo (by exact zero_ne_one)]
    exact ⟨le_rfl,zero_le_one⟩
  obtain ⟨t,htW,ht⟩ := (mem_closure_iff_nhds.mp h₀cl) (a ⁻¹' W)
    ((hW.preimage a.continuous).mem_nhds h₀W)
  have hld (i : Bool) : l i=d := by
    apply hb (a t) htW
    rw [hl t ht.1 ht.2]
    exact mem_range_self i
  refine ⟨d,fun z => ?_⟩
  have hV : IsOpen (U\range a) := hU.sdiff a.compact_range.isClosed
  have hne : (U\(U\range a)).Nonempty := ⟨a 0,ha₀,fun h => h.2 (mem_range_self 0)⟩
  obtain ⟨x,⟨hxU,hxV⟩,hxe⟩ := region_boundary_hits_in_open hU hV sdiff_subset hconn hne hπ (π z)
    ⟨z,z.property,rfl⟩
  have hxa : x∈range a := by by_contra h; exact hxV ⟨hxU,h⟩
  obtain ⟨s,rfl⟩ := hxa
  by_cases hs₀ : s=0
  · subst s
    exact hb (a 0) h₀W hxe
  · have hs₁ : s≠1 := by intro he; subst s; exact ha₁ hxU
    rw [hl s (lt_of_le_of_ne (unitInterval.nonneg s) (fun h => hs₀ h.symm))
      (lt_of_le_of_ne (unitInterval.le_one s) hs₁)] at hxe
    obtain ⟨i,hi⟩ := hxe
    exact hi.symm.trans (hld i)

theorem tame_slit_connected (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (ha₀ : a 0∈U) (hUa : a '' Ioo (0:I) 1⊆U) (ha₁ : a 1∉U) :
    IsConnected (U\range a) := by
  have hV : IsOpen (U\range a) := hU.sdiff a.compact_range.isClosed
  let _ : LocallyConnectedSpace (U\range a : Set ℂ) := hV.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (U\range a : Set ℂ)) := inferInstance
  obtain ⟨d,hd⟩ := slit_discrete_labels_constant a Q ha hU hconn ha₀ hUa ha₁
    ConnectedComponents.continuous_coe
  have hp : PreconnectedSpace (U\range a : Set ℂ) := by
    rw [preconnectedSpace_iff_connectedComponent]
    intro x
    apply eq_univ_of_forall
    intro y
    exact ConnectedComponents.coe_eq_coe'.mp ((hd y).trans (hd x).symm)
  have hn : (U\range a).Nonempty := by
    obtain ⟨W,_,_,hWU,hWconn⟩ := tame_tip_connected_neighborhood a Q ha hU ha₀
    obtain ⟨x,hxW,hxa⟩ := hWconn.nonempty
    exact ⟨x,hWU hxW,hxa⟩
  exact ⟨hn,isPreconnected_iff_preconnectedSpace.mpr hp⟩
end CannonEmbeddedArc.Arc

namespace CannonPolygonal
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polyJoined_of_preconnected_finite_segments (Q : Finset (E×E))
    (hK : IsPreconnected (⋃ q∈Q,segment ℝ q.1 q.2))
    {x y : E} (hx : x∈⋃ q∈Q,segment ℝ q.1 q.2)
    (hy : y∈⋃ q∈Q,segment ℝ q.1 q.2) :
    PolyJoined (⋃ q∈Q,segment ℝ q.1 q.2) x y := by
  classical
  let K := ⋃ q∈Q,segment ℝ q.1 q.2
  let V := ⋃ q∈Q.filter (fun q => PolyJoined K x q.1),segment ℝ q.1 q.2
  let W := ⋃ q∈Q.filter (fun q => ¬PolyJoined K x q.1),segment ℝ q.1 q.2
  have hseg (q : E×E) (hq : q∈Q) : segment ℝ q.1 q.2⊆K :=
    subset_iUnion₂_of_subset q hq Subset.rfl
  have hreach (q : E×E) (hq : q∈Q) {z : E} (hz : z∈segment ℝ q.1 q.2) :
      PolyJoined K x z ↔ PolyJoined K x q.1 := by
    constructor
    · intro h
      exact h.tail (((convex_segment q.1 q.2 : Convex ℝ _).segment_subset hz (left_mem_segment ..)).trans (hseg q hq))
    · intro h
      exact h.tail (((convex_segment q.1 q.2 : Convex ℝ _).segment_subset (left_mem_segment ..) hz).trans (hseg q hq))
  have hV (z : E) : z∈V ↔ z∈K ∧ PolyJoined K x z := by
    constructor
    · intro hz
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      obtain ⟨hq,hqr⟩ := Finset.mem_filter.mp hq
      exact ⟨hseg q hq hzq,(hreach q hq hzq).mpr hqr⟩
    · rintro ⟨hz,hr⟩
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,(hreach q hq hzq).mp hr⟩,hzq⟩
  have hW (z : E) : z∈W ↔ z∈K ∧ ¬PolyJoined K x z := by
    constructor
    · intro hz
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      obtain ⟨hq,hqr⟩ := Finset.mem_filter.mp hq
      exact ⟨hseg q hq hzq,fun h => hqr ((hreach q hq hzq).mp h)⟩
    · rintro ⟨hz,hr⟩
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,fun h => hr ((hreach q hq hzq).mpr h)⟩,hzq⟩
  have hcV : IsClosed V := isClosed_biUnion_finset fun q _ => by
    have hh := (isCompact_range (Path.segment q.1 q.2).continuous).isClosed
    simpa only [Path.range_segment] using hh
  have hcW : IsClosed W := isClosed_biUnion_finset fun q _ => by
    have hh := (isCompact_range (Path.segment q.1 q.2).continuous).isClosed
    simpa only [Path.range_segment] using hh
  by_contra hn
  have hcover : K⊆V∪W := by
    intro z hz
    by_cases hr : PolyJoined K x z
    · exact Or.inl ((hV z).mpr ⟨hz,hr⟩)
    · exact Or.inr ((hW z).mpr ⟨hz,hr⟩)
  obtain ⟨z,hzK,hzV,hzW⟩ := isPreconnected_closed_iff.mp hK V W hcV hcW hcover
    ⟨x,hx,(hV x).mpr ⟨hx,.refl⟩⟩ ⟨y,hy,(hW y).mpr ⟨hy,hn⟩⟩
  exact ((hW z).mp hzW).2 ((hV z).mp hzV).2

theorem preconnected_finite_segments_arc (Q : Finset (E×E))
    (hK : IsPreconnected (⋃ q∈Q,segment ℝ q.1 q.2))
    {x y : E} (hx : x∈⋃ q∈Q,segment ℝ q.1 q.2)
    (hy : y∈⋃ q∈Q,segment ℝ q.1 q.2) (hne : x≠y) :
    ∃ a : CannonEmbeddedArc.Arc E, a 0=x ∧ a 1=y ∧
      range a⊆⋃ q∈Q,segment ℝ q.1 q.2 ∧ FiniteSupport (range a) :=
  polyJoined_arc (polyJoined_of_preconnected_finite_segments Q hK hx hy) hne
end CannonPolygonal

namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence

theorem connected_graph_crosscut (P Q : Finset (ℂ × ℂ))
    (hK : IsPreconnected (⋃ p∈P,segment ℝ p.1 p.2))
    (a : Arc ℂ) (ha : range a⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (ha₀ : a 0∈⋃ p∈P,segment ℝ p.1 p.2)
    (ha₁ : a 1∈⋃ p∈P,segment ℝ p.1 p.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hUK : U⊆(⋃ p∈P,segment ℝ p.1 p.2)ᶜ)
    (hUa : a '' Ioo (0:I) 1⊆U) :
    ∃ l : Bool ≃ ConnectedComponents (U\range a : Set ℂ),
      ∀ t : I, 0<t → t<1 → incident (U\range a) ConnectedComponents.mk (a t)=range l := by
  classical
  obtain ⟨b,hb₀,hb₁,hbK,hbS⟩ := CannonPolygonal.preconnected_finite_segments_arc P hK ha₀ ha₁ a.endpoints_ne
  obtain ⟨R,hbR⟩ := hbS
  have hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := by
    intro s t he
    have hs : s=0 ∨ s=1 := by
      by_contra hn
      have hs₀ : s≠0 := fun h => hn (Or.inl h)
      have hs₁ : s≠1 := fun h => hn (Or.inr h)
      exact hUK (hUa ⟨s,⟨lt_of_le_of_ne (show (0:I) ≤ s from s.property.1) (Ne.symm hs₀),
        lt_of_le_of_ne (le_one s) hs₁⟩,rfl⟩) (he ▸ hbK (mem_range_self t))
    refine ⟨hs,?_⟩
    rcases hs with rfl|rfl
    · exact Or.inl (b.injective (he.symm.trans hb₀.symm))
    · exact Or.inr (b.injective (he.symm.trans hb₁.symm))
  have ha' : range a⊆⋃ q∈Q∪R,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp (ha hz)
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_union_left R hq,hzq⟩
  have hb' : range b⊆⋃ q∈Q∪R,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp (hbR hz)
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_union_right Q hq,hzq⟩
  exact tame_crosscut_components a b hb₀.symm hb₁.symm hc (Q∪R) ha' hb' hU hconn hUa
    (fun z hz hzU => hUK hzU (hbK hz))
end CannonEmbeddedArc.Arc

namespace CannonSegmentCones
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def RadialStable (K : Set E) (x : E) (ε : ℝ) : Prop :=
  ∀ y, dist y x < ε → ∀ t : ℝ, 0 < t → t ≤ 1 →
    (x + t • (y-x) ∈ K ↔ y ∈ K)

lemma radial_dist (x y : E) {t : ℝ} (ht : 0 ≤ t) :
    dist (x+t • (y-x)) x=t*dist y x := by
  simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]

lemma radial_mem_ball {x y : E} {ε t : ℝ} (hy : dist y x < ε)
    (ht : 0 ≤ t) (ht₁ : t ≤ 1) : dist (x+t • (y-x)) x < ε := by
  rw [radial_dist x y ht]
  exact (mul_le_of_le_one_left dist_nonneg ht₁).trans_lt hy

lemma segment_split {a b x : E} (hx : x ∈ segment ℝ a b) :
    segment ℝ a b=segment ℝ x a ∪ segment ℝ x b := by
  apply Subset.antisymm
  · intro z hz
    by_cases hza : z=a
    · exact Or.inl (hza ▸ right_mem_segment ℝ x a)
    by_cases hzb : z=b
    · exact Or.inr (hzb ▸ right_mem_segment ℝ x b)
    have hzo := mem_openSegment_of_ne_left_right (Ne.symm hza) (Ne.symm hzb) hz
    have hxr : x ∈ range (AffineMap.lineMap a b : ℝ → E) := by
      rw [segment_eq_image_lineMap] at hx
      exact image_subset_range _ _ hx
    rcases openSegment_subset_union a b hxr hzo with he|ha|hb
    · exact Or.inl (he ▸ left_mem_segment ℝ x a)
    · exact Or.inl (segment_symm ℝ a x ▸ openSegment_subset_segment ℝ _ _ ha)
    · exact Or.inr (openSegment_subset_segment ℝ _ _ hb)
  · exact union_subset
      ((convex_segment (𝕜:=ℝ) a b).segment_subset hx (left_mem_segment ℝ a b))
      ((convex_segment (𝕜:=ℝ) a b).segment_subset hx (right_mem_segment ℝ a b))

lemma anchored_radial_stable (x a : E) :
    ∃ ε>0, RadialStable (segment ℝ x a) x ε := by
  by_cases ha : a=x
  · subst a
    refine ⟨1,zero_lt_one,?_⟩
    intro y hy t ht ht₁
    simp only [segment_same,mem_singleton_iff,add_eq_left]
    rw [smul_eq_zero]
    simp [ht.ne',sub_eq_zero]
  · refine ⟨‖a-x‖,norm_pos_iff.mpr (sub_ne_zero.mpr ha),?_⟩
    intro y hy t ht ht₁
    constructor
    · intro hz
      rw [segment_eq_image'] at hz ⊢
      obtain ⟨s,hs,he⟩ := hz
      have he' : s • (a-x)=t • (y-x) := by
        simpa only [add_right_inj] using he
      have hv : y-x=(s/t) • (a-x) := by
        calc
          y-x=t⁻¹ • (t • (y-x)) := by simp [smul_smul,ht.ne']
          _=t⁻¹ • (s • (a-x)) := by rw [he']
          _=(s/t) • (a-x) := by rw [smul_smul,div_eq_inv_mul]
      have hst₀ : 0 ≤ s/t := div_nonneg hs.1 ht.le
      have hst₁ : s/t ≤ 1 := by
        have hn := congrArg norm hv
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hst₀] at hn
        rw [dist_eq_norm] at hy
        have han : 0 < ‖a-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
        nlinarith
      refine ⟨s/t,⟨hst₀,hst₁⟩,?_⟩
      change x+(s/t) • (a-x)=y
      rw [←hv,add_sub_cancel]
    · intro hyseg
      have hz := (convex_segment (𝕜:=ℝ) x a) (left_mem_segment ℝ x a) hyseg
        (sub_nonneg.mpr ht₁) ht.le (sub_add_cancel 1 t)
      convert hz using 1; module

lemma RadialStable.mono_radius {K : Set E} {x : E} {ε δ : ℝ}
    (h : RadialStable K x ε) (hδε : δ ≤ ε) : RadialStable K x δ :=
  fun y hy t ht ht₁ => h y (hy.trans_le hδε) t ht ht₁

lemma RadialStable.union {K L : Set E} {x : E} {ε δ : ℝ}
    (hK : RadialStable K x ε) (hL : RadialStable L x δ) :
    RadialStable (K∪L) x (min ε δ) := by
  intro y hy t ht ht₁
  simp only [mem_union]
  rw [hK y (hy.trans_le (min_le_left _ _)) t ht ht₁,
    hL y (hy.trans_le (min_le_right _ _)) t ht ht₁]

lemma segment_closed (a b : E) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image']
  exact (isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))).isClosed

lemma segment_radial_stable (a b x : E) :
    ∃ ε>0, RadialStable (segment ℝ a b) x ε := by
  by_cases hx : x∈segment ℝ a b
  · obtain ⟨ε,hε,hεK⟩ := anchored_radial_stable x a
    obtain ⟨δ,hδ,hδK⟩ := anchored_radial_stable x b
    refine ⟨min ε δ,lt_min hε hδ,?_⟩
    rw [segment_split hx]
    exact hεK.union hδK
  · obtain ⟨ε,hε,hεK⟩ := Metric.isOpen_iff.mp (segment_closed a b).isOpen_compl x hx
    refine ⟨ε,hε,?_⟩
    intro y hy t ht ht₁
    have hyK := hεK hy
    have hzK := hεK (radial_mem_ball hy ht.le ht₁)
    exact iff_of_false hzK hyK

theorem finite_segments_radial_stable (Q : Finset (E×E)) (x : E) :
    ∃ ε>0, RadialStable (⋃ q∈Q,segment ℝ q.1 q.2) x ε := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp [RadialStable]⟩
  | @insert q Q hq ih =>
    obtain ⟨ε,hε,hεK⟩ := segment_radial_stable q.1 q.2 x
    obtain ⟨δ,hδ,hδK⟩ := ih
    refine ⟨min ε δ,lt_min hε hδ,?_⟩
    simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using hεK.union hδK

theorem component_radial_access (Q : Finset (E×E)) {x a : E}
    (hxK : x ∈ ⋃ q∈Q,segment ℝ q.1 q.2)
    (hx : x∈closure (connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ a)) :
    ∃ y : E, y≠x ∧ ∀ t : ℝ, 0<t → t≤1 →
      x+t • (y-x)∈connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ a := by
  let K : Set E := ⋃ q∈Q,segment ℝ q.1 q.2
  obtain ⟨ε,hε,hstable⟩ := finite_segments_radial_stable Q x
  obtain ⟨y,hyball,hy⟩ := (mem_closure_iff_nhds.mp hx)
    (Metric.ball x ε) (Metric.ball_mem_nhds x hε)
  have hyK : y∉K := connectedComponentIn_subset _ _ hy
  have hyx : y≠x := fun h => hyK (h ▸ hxK)
  let S : Set E := (fun t : ℝ => x+t • (y-x)) '' Ioc 0 1
  have hS : IsPreconnected S := isPreconnected_Ioc.image _ (by fun_prop)
  have hyS : y∈S := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
  have hSK : S⊆Kᶜ := by
    rintro z ⟨t,ht,rfl⟩ hz
    exact hyK ((hstable y hyball t ht.1 ht.2).mp hz)
  have hsub := hS.subset_connectedComponentIn hyS hSK
  rw [←connectedComponentIn_eq hy] at hsub
  refine ⟨y,hyx,fun t ht ht₁ => hsub ⟨t,⟨ht,ht₁⟩,rfl⟩⟩

end CannonSegmentCones
namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonPolygonal CannonSegmentCones

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Finite ι]

theorem finite_graph_exact_segments (F : ι → Arc E)
    (Q : Finset (E×E)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2) :
    ∃ P : Finset (E×E), (⋃ i,range (F i))=⋃ p∈P,segment ℝ p.1 p.2 := by
  classical
  let _ := Fintype.ofFinite ι
  choose P hP₀ hP₁ hPs using fun i => finite_segment_arc_subdivision Q (F i) (hQ i)
  let R : Finset (E×E) := Finset.univ.biUnion fun i =>
    (segments (P i)).image (fun z => (F i z.1,F i z.2))
  refine ⟨R,?_⟩
  have he (i : ι) : range (F i)=⋃ z : segments (P i),
      segment ℝ (F i z.val.1) (F i z.val.2) := by
    rw [subdivision_cover (F i) (P i) (hP₀ i) (hP₁ i)]
    exact iUnion_congr fun z => hPs i z
  simp only [he]
  ext x
  constructor
  · intro hx
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    obtain ⟨z,hz⟩ := mem_iUnion.mp hxi
    apply mem_iUnion₂.mpr
    refine ⟨(F i z.val.1,F i z.val.2),?_,hz⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,
      Finset.mem_image.mpr ⟨z.val,z.property,rfl⟩⟩
  · intro hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨z,hz⟩,hxp⟩⟩

lemma halfopen_radial_segment {U : Set E} {x y : E}
    (h : ∀ t : ℝ, 0<t → t≤1 → x+t • (y-x)∈U) :
    segment ℝ x y⊆insert x U := by
  rw [segment_eq_image']
  rintro z ⟨t,ht,rfl⟩
  rcases eq_or_lt_of_le ht.1 with he|he
  · simp [←he]
  · exact Or.inr (h t he ht.2)

theorem arc_to_accessible_point {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y z : E} (hx : x∉U) (hz : z∈U)
    (haccess : ∀ t : ℝ, 0<t → t≤1 → x+t • (y-x)∈U) :
    ∃ a : Arc E, a 0=x ∧ a 1=z ∧ (∀ t : I, t≠0 → a t∈U) ∧
      FiniteSupport (range a) := by
  have hy : y∈U := by simpa using haccess 1 zero_lt_one le_rfl
  have hj : PolyJoined (insert x U) x z := by
    have hxy : PolyJoined (insert x U) x y :=
      Relation.ReflTransGen.single (halfopen_radial_segment haccess)
    apply hxy.trans
    exact Relation.ReflTransGen.mono
      (r:=fun a b => segment ℝ a b⊆U) (p:=fun a b => segment ℝ a b⊆insert x U)
      (fun _ _ h => h.trans (subset_insert x U)) y z
      (polyJoined_of_open_preconnected hU hc hy hz)
  obtain ⟨a,ha₀,ha₁,haS,haF⟩ := polyJoined_arc hj (fun he => hx (he ▸ hz))
  refine ⟨a,ha₀,ha₁,?_,haF⟩
  intro t ht
  rcases haS (mem_range_self t) with h|h
  · exact (ht (a.injective (h.trans ha₀.symm))).elim
  · exact h

theorem tame_component_accessible (F : ι → Arc E)
    (Q : Finset (E×E)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {x z : E} (hx : x∈⋃ i,range (F i)) (hz : z∉⋃ i,range (F i))
    (hcl : x∈closure (connectedComponentIn (⋃ i,range (F i))ᶜ z)) :
    ∃ a : Arc E, a 0=x ∧ a 1=z ∧
      (∀ t : I, t≠0 → a t∈connectedComponentIn (⋃ i,range (F i))ᶜ z) ∧
      FiniteSupport (range a) := by
  obtain ⟨P,hP⟩ := finite_graph_exact_segments F Q hQ
  rw [hP] at hx hz hcl ⊢
  obtain ⟨y,hy,haccess⟩ := component_radial_access P hx hcl
  have hK : IsClosed (⋃ p∈P,segment ℝ p.1 p.2) :=
    isClosed_biUnion_finset (fun p hp => segment_closed p.1 p.2)
  have hxU : x∉connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ z := by
    intro hh
    exact (connectedComponentIn_subset _ _ hh) hx
  exact arc_to_accessible_point hK.isOpen_compl.connectedComponentIn
    isPreconnected_connectedComponentIn hxU (mem_connectedComponentIn hz) haccess
end CannonEmbeddedArc.Arc
namespace CannonSegmentCones
open Set Metric Topology

lemma complex_segment_supporting_line (a b : ℂ) :
    ∃ f : ℂ →L[ℝ] ℝ, f≠0 ∧ segment ℝ a b⊆{x | f x=f a} := by
  let x₀ := Complex.reCLM
  let x₁ := Complex.imCLM
  by_cases hd : b.re=a.re
  · refine ⟨x₀,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f 1) h
      norm_num [x₀] at hh
    · exact ((convex_singleton (x₀ a)).linear_preimage x₀.toLinearMap).segment_subset rfl hd
  · let f := x₁-((b.im-a.im)/(b.re-a.re)) • x₀
    refine ⟨f,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f Complex.I) h
      norm_num [f,x₀,x₁] at hh
    · have hab : f b=f a := by
        change b.im-((b.im-a.im)/(b.re-a.re))*b.re=a.im-((b.im-a.im)/(b.re-a.re))*a.re
        have hn := sub_ne_zero.mpr hd
        field_simp [hn]
        ring
      exact ((convex_singleton (f a)).linear_preimage f.toLinearMap).segment_subset rfl hab

lemma complex_finite_segments_compl_dense (Q : Finset (ℂ × ℂ)) :
    Dense ((⋃ q∈Q,segment ℝ q.1 q.2)ᶜ : Set ℂ) := by
  classical
  choose f hf hfs using fun q : Q => complex_segment_supporting_line q.val.1 q.val.2
  have hsurj (q : Q) : Function.Surjective (f q) := by
    obtain ⟨v,hv⟩ : ∃ v, f q v≠0 := by
      by_contra hn
      push Not at hn
      apply hf q
      ext v
      exact hn v
    intro y
    refine ⟨(y/f q v) • v,?_⟩
    simp only [map_smul,smul_eq_mul]
    exact div_mul_cancel₀ y hv
  have hopen (q : Q) : IsOpen {x | f q x≠f q q.val.1} :=
    isOpen_compl_singleton.preimage (f q).continuous
  have hdense (q : Q) : Dense {x | f q x≠f q q.val.1} :=
    (dense_compl_singleton _).preimage ((f q).isOpenMap (hsurj q))
  have hd := dense_iInter_of_isOpen hopen hdense
  apply hd.mono
  intro z hz hzQ
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hzQ
  exact (mem_iInter.mp hz ⟨q,hq⟩) (hfs ⟨q,hq⟩ hzq)

theorem refined_component_at_boundary (P Q : Finset (ℂ × ℂ))
    (hPQ : (⋃ p∈P,segment ℝ p.1 p.2)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {a x : ℂ} (ha : a∉⋃ p∈P,segment ℝ p.1 p.2)
    (hx : x∈closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)) :
    ∃ z∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a,
      z∉⋃ q∈Q,segment ℝ q.1 q.2 ∧
      x∈closure (connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ z) ∧
      connectedComponentIn (⋃ q∈Q,segment ℝ q.1 q.2)ᶜ z⊆
        connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a := by
  let K := ⋃ p∈P,segment ℝ p.1 p.2
  let L := ⋃ q∈Q,segment ℝ q.1 q.2
  let U := connectedComponentIn Kᶜ a
  have hK : IsClosed K := isClosed_biUnion_finset (fun p _ => segment_closed p.1 p.2)
  have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
  obtain ⟨ε,hε,hstable⟩ := finite_segments_radial_stable Q x
  have hne : (ball x ε∩U).Nonempty := mem_closure_iff_nhds.mp hx _ (ball_mem_nhds x hε)
  obtain ⟨z,⟨hzball,hzU⟩,hzL⟩ := (complex_finite_segments_compl_dense Q).inter_open_nonempty
    _ (isOpen_ball.inter hU) hne
  let S : Set ℂ := (fun t : ℝ => x+t • (z-x)) '' Ioc 0 1
  have hS : IsPreconnected S := isPreconnected_Ioc.image _ (by fun_prop)
  have hzS : z∈S := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
  have hSL : S⊆Lᶜ := by
    rintro w ⟨t,ht,rfl⟩ hw
    exact hzL ((hstable z hzball t ht.1 ht.2).mp hw)
  have hSR : S⊆connectedComponentIn Lᶜ z := hS.subset_connectedComponentIn hzS hSL
  have hxS : x∈closure S := by
    have h₀ : (0:ℝ)∈closure (Ioc (0:ℝ) 1) := by rw [closure_Ioc zero_ne_one]; exact ⟨le_rfl,zero_le_one⟩
    have hh := image_closure_subset_closure_image (s:=Ioc (0:ℝ) 1) (show Continuous (fun t : ℝ => x+t • (z-x)) by fun_prop)
    exact hh ⟨0,h₀,by simp⟩
  have hsub : connectedComponentIn Lᶜ z⊆U := by
    have hLK : Lᶜ⊆Kᶜ := compl_subset_compl.mpr hPQ
    have hconn : IsPreconnected (U ∪ connectedComponentIn Lᶜ z) :=
      IsPreconnected.union z hzU (mem_connectedComponentIn hzL)
        isPreconnected_connectedComponentIn isPreconnected_connectedComponentIn
    exact subset_union_right.trans (hconn.subset_connectedComponentIn
      (Or.inl (mem_connectedComponentIn ha))
      (union_subset (connectedComponentIn_subset _ _)
        ((connectedComponentIn_subset _ _).trans hLK)))
  exact ⟨z,hzU,hzL,closure_mono hSR hxS,hsub⟩
end CannonSegmentCones

namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonPolygonal CannonSegmentCones

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem arc_between_accessible_points {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y a b : E} (hxy : x≠y)
    (hax : ∀ t : ℝ, 0<t → t≤1 → x+t • (a-x)∈U)
    (hby : ∀ t : ℝ, 0<t → t≤1 → y+t • (b-y)∈U) :
    ∃ c : Arc E, c 0=x ∧ c 1=y ∧ (∀ t : I, t≠0 → t≠1 → c t∈U) ∧
      FiniteSupport (range c) := by
  let V := insert x (insert y U)
  have ha : a∈U := by simpa using hax 1 zero_lt_one le_rfl
  have hb : b∈U := by simpa using hby 1 zero_lt_one le_rfl
  have hUV : U⊆V := (subset_insert y U).trans (subset_insert x _)
  have hxa : PolyJoined V x a := Relation.ReflTransGen.single
    ((halfopen_radial_segment hax).trans (insert_subset (mem_insert _ _) hUV))
  have hab : PolyJoined V a b := Relation.ReflTransGen.mono
    (r:=fun a b => segment ℝ a b⊆U) (p:=fun a b => segment ℝ a b⊆V)
    (fun _ _ h => h.trans hUV) a b (polyJoined_of_open_preconnected hU hc ha hb)
  have hby' : PolyJoined V b y := Relation.ReflTransGen.single (by
    rw [segment_symm]
    exact (halfopen_radial_segment hby).trans (insert_subset (by simp [V]) hUV))
  obtain ⟨c,hc₀,hc₁,hcV,hcS⟩ := polyJoined_arc (hxa.trans (hab.trans hby')) hxy
  refine ⟨c,hc₀,hc₁,?_,hcS⟩
  intro t ht₀ ht₁
  rcases hcV (mem_range_self t) with h|h|h
  · exact (ht₀ (c.injective (h.trans hc₀.symm))).elim
  · exact (ht₁ (c.injective (h.trans hc₁.symm))).elim
  · exact h

theorem finite_segment_component_crosscut (P : Finset (E×E))
    {x y z : E} (hx : x∈⋃ p∈P,segment ℝ p.1 p.2)
    (hy : y∈⋃ p∈P,segment ℝ p.1 p.2) (hxy : x≠y)
    (hxcl : x∈closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ z))
    (hycl : y∈closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ z)) :
    ∃ c : Arc E, c 0=x ∧ c 1=y ∧
      (∀ t : I, t≠0 → t≠1 → c t∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ z) ∧
      FiniteSupport (range c) := by
  obtain ⟨a,_,ha⟩ := component_radial_access P hx hxcl
  obtain ⟨b,_,hb⟩ := component_radial_access P hy hycl
  have hK : IsClosed (⋃ p∈P,segment ℝ p.1 p.2) :=
    isClosed_biUnion_finset (fun p _ => segment_closed p.1 p.2)
  exact arc_between_accessible_points hK.isOpen_compl.connectedComponentIn
    isPreconnected_connectedComponentIn hxy ha hb
end CannonEmbeddedArc.Arc

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
