import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.TraceBounds

namespace OAI

/-! Corridors for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorEligibility
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem edge_has_label (w : RawCorridor G k) (s : Sym2 V) (hs : s ∈ w.path.edges) :
    ∃ e ∈ w.retained, G e = s := by
  induction s using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨_,e,_,he⟩ := w.path.adj_of_mem_edges hs
    exact ⟨e,by simpa only [retained,Set.mem_ofPred_eq,he] using hs,he⟩

theorem image_retained (w : RawCorridor G k) : G '' w.retained = {s | s ∈ w.path.edges} := by
  ext s
  constructor
  · rintro ⟨e,he,rfl⟩; exact he
  · exact w.edge_has_label s

theorem retained_ncard (hG : Function.Injective G) (w : RawCorridor G k) :
    w.retained.ncard = w.path.length := by
  rw [←hG.injOn.ncard_image (s := w.retained),w.image_retained]
  have hh := List.toFinset_card_of_nodup w.path_isPath.isTrail.edges_nodup
  simpa only [←List.coe_toFinset,Set.ncard_coe_finset,SimpleGraph.Walk.length_edges] using hh

 

theorem support_subset_of_retained (w : RawCorridor G k) (hlen : 0 < w.path.length)
    (D : Set V) (he : w.retained ⊆ internalEdges G D) :
    ∀ z ∈ w.path.support, z ∈ D := by
  intro z hz
  obtain ⟨s,hs,hzs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hlen)).mp hz
  obtain ⟨e,he',hGe⟩ := w.edge_has_label s hs
  exact he he' z (hGe.symm ▸ hzs)

theorem retained_subset_of_support (w : RawCorridor G k) (D : Set V)
    (hs : ∀ z ∈ w.path.support, z ∈ D) : w.retained ⊆ internalEdges G D := by
  intro e he z hz
  exact hs z (SimpleGraph.Walk.mem_support_of_mem_edges he hz)

theorem support_iff_retained (w : RawCorridor G k) (hlen : 0 < w.path.length) (D : Set V) :
    (∀ z ∈ w.path.support, z ∈ D) ↔ w.retained ⊆ internalEdges G D :=
  ⟨w.retained_subset_of_support D,w.support_subset_of_retained hlen D⟩

theorem retained_incident_interior (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (e : E) (he : e ∈ w.retained) : ∃ z ∈ w.interior, z ∈ G e := by
  change G e ∈ w.path.edges at he
  generalize hab : G e = s at he
  induction s using Sym2.inductionOn with
  | _ a b =>
    have hedge : s(a,b) ∈ w.path.edges := he
    have ha := w.path.fst_mem_support_of_mem_edges hedge
    have hb := w.path.snd_mem_support_of_mem_edges hedge
    have habne : a ≠ b := (w.path.adj_of_mem_edges hedge).1
    by_contra hn
    have hna : a ∉ w.interior := fun hi => hn ⟨a,hi,by simp⟩
    have hnb : b ∉ w.interior := fun hi => hn ⟨b,hi,by simp⟩
    have hax : a = w.base ∨ a = w.endpoint := by simpa only [interior,Finset.mem_sdiff,List.mem_toFinset,ha,true_and,Finset.mem_insert,Finset.mem_singleton,not_not] using hna
    have hbx : b = w.base ∨ b = w.endpoint := by simpa only [interior,Finset.mem_sdiff,List.mem_toFinset,hb,true_and,Finset.mem_insert,Finset.mem_singleton,not_not] using hnb
    have hedge' : s(w.base,w.endpoint) ∈ w.path.edges := by
      rcases hax with rfl | rfl <;> rcases hbx with rfl | rfl
      · exact (habne rfl).elim
      · exact hedge
      · simpa only [Sym2.eq_swap] using hedge
      · exact (habne rfl).elim
    have hh := w.path_isPath.length_eq_one_of_mem_edges hedge'
    omega

theorem specified_disjoint_exterior (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) :
    Disjoint (w.retained ∪ w.blockers) (internalEdges G (w.interior : Set V)ᶜ) := by
  apply Set.disjoint_left.mpr
  intro e he hx
  obtain ⟨z,hz,he⟩ := he.elim (w.retained_incident_interior hlen e) (fun hb => hb.1)
  exact hx z he hz

end RawCorridor
end CorridorEligibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExactCorridorPattern
attribute [local instance] Classical.propDecidable Classical.decEq

def edgePattern (A B : Finset E) : Set (Set E) :=
  {ω | (A : Set E) ⊆ ω ∧ Disjoint (B : Set E) ω}

theorem edgePattern_eq_restriction (A B : Finset E) (hAB : Disjoint A B) :
    edgePattern A B = {ω | ω ∩ ((A ∪ B : Finset E) : Set E) = (A : Set E)} := by
  ext ω
  constructor
  · rintro ⟨ha,hb⟩
    apply Set.Subset.antisymm
    · rintro e ⟨he,heQ⟩
      rcases Finset.mem_union.mp heQ with h | h
      · exact h
      · exact (Set.disjoint_left.mp hb h he).elim
    · intro e he
      exact ⟨ha he,Finset.mem_union_left _ he⟩
  · intro h
    constructor
    · intro e he
      exact ((Set.ext_iff.mp h e).mpr he).1
    · apply Set.disjoint_left.mpr
      intro e he hw
      have ha : e ∈ A := (Set.ext_iff.mp h e).mp ⟨hw,Finset.mem_union_right _ he⟩
      exact Finset.disjoint_left.mp hAB ha he

theorem measurableSet_edgePattern (A B : Finset E) (hAB : Disjoint A B) :
    MeasurableSet (edgePattern A B) := by
  rw [edgePattern_eq_restriction A B hAB]
  exact measurableSet_finite_restriction (A∪B) {(A:Set E)}

 
theorem edgePattern_probability (A B : Finset E) (hAB : Disjoint A B) (p : unitInterval) :
    (law p).real (edgePattern A B) = (p:ℝ)^A.card*(1-(p:ℝ))^B.card := by
  let f : Set E → ℝ := fun ω => if ω ∈ edgePattern A B then 1 else 0
  have hf (ω : Set E) : f ω = f (ω ∩ ((A∪B:Finset E):Set E)) := by
    simp only [f,edgePattern_eq_restriction A B hAB,Set.mem_ofPred_eq,Set.inter_assoc,Set.inter_self]
  rw [←integral_event_indicator p _ (measurableSet_edgePattern A B hAB)]
  change (∫ ω, f ω ∂law p) = _
  rw [integral_eq_bernoulliPolynomial (A∪B) p f hf]
  trans bernoulliPolynomial (A∪B) (fun η => if η=A then 1 else 0) p
  · apply bernoulliPolynomial_congr
    intro η hη
    have he : (η:Set E) ∩ ((A∪B:Finset E):Set E) = (η:Set E) :=
      Set.inter_eq_left.mpr hη
    simp only [f,edgePattern_eq_restriction A B hAB,Set.mem_ofPred_eq,he,Finset.coe_inj]
  · simp only [bernoulliPolynomial,ite_mul,zero_mul,one_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_powerset,Finset.subset_union_left,ite_true,Finset.card_union_of_disjoint hAB,
      Nat.add_sub_cancel_left]

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def calibrationEvent (w : RawCorridor G k) : Set (Set E) :=
  {ω | w.retained ⊆ ω ∧ Disjoint w.blockers ω}

theorem calibrationEvent_eq (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) : w.calibrationEvent =
      edgePattern (w.retained_finite hG).toFinset (w.blockers_finite hloc).toFinset := by
  simp only [calibrationEvent,edgePattern,Set.Finite.coe_toFinset]

theorem calibration_probability (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (p : unitInterval) :
    (law p).real w.calibrationEvent = (p:ℝ)^w.path.length*(1-(p:ℝ))^w.blockers.ncard := by
  rw [w.calibrationEvent_eq hG hloc,edgePattern_probability]
  · rw [←Set.ncard_eq_toFinset_card w.retained (w.retained_finite hG),←Set.ncard_eq_toFinset_card w.blockers (w.blockers_finite hloc),w.retained_ncard hG]
  · apply Finset.disjoint_left.mpr
    intro e he hb
    exact Set.disjoint_left.mp w.retained_disjoint_blockers
      ((w.retained_finite hG).mem_toFinset.mp he) ((w.blockers_finite hloc).mem_toFinset.mp hb)

 

theorem calibration_identity (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (P : V → V → ℝ) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) :
    w.weight P p * (law p).real w.calibrationEvent = w.probability P := by
  rw [w.calibration_probability hG hloc p]
  unfold weight
  have h₁ := pow_ne_zero w.path.length hp.ne'
  have h₂ := pow_ne_zero w.blockers.ncard (sub_pos.mpr hp₁).ne'
  field_simp

end RawCorridor
end ExactCorridorPattern
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorTerminalGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem path_internal_two_neighbors {H : SimpleGraph V} {u v z : V}
    (q : H.Walk u v) (hq : q.IsPath) (hz : z ∈ q.support) (hzu : z ≠ u) (hzv : z ≠ v) :
    ∃ a b : V, a ≠ b ∧ s(z,a) ∈ q.edges ∧ s(z,b) ∈ q.edges := by
  induction q with
  | nil => simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hz; exact (hzu hz).elim
  | @cons u a v h q ih =>
    have htail : q.IsPath := hq.of_cons
    have huz : u ∉ q.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hq).2
    have hzq : z ∈ q.support := (List.mem_cons.mp hz).resolve_left hzu
    by_cases hza : z = a
    · subst z
      cases q with
      | nil => exact (hzv rfl).elim
      | @cons a b v h' q =>
        refine ⟨u,b,?_,?_,?_⟩
        · intro hub
          apply huz
          subst b
          simp
        · simp only [SimpleGraph.Walk.edges_cons,List.mem_cons,Sym2.eq_swap]; exact Or.inl trivial
        · simp only [SimpleGraph.Walk.edges_cons,List.mem_cons]; exact Or.inr (Or.inl trivial)
    · obtain ⟨b,c,hbc,hb,hc⟩ := ih htail hzq hza hzv
      exact ⟨b,c,hbc,List.mem_cons_of_mem _ hb,List.mem_cons_of_mem _ hc⟩

 

theorem pivotal_image_mem_edges (G : BondGraph V E) (ω : Set E) {x y : V}
    (q : (openSimpleGraph G ω).Walk x y) (e : E)
    (hp : ¬Conn G (ω \ {e}) x y) : G e ∈ q.edges := by
  obtain ⟨l,hl,hmap,ho⟩ := walk_lift_bonds G ω q
  by_contra he
  apply hp
  apply hl.conn
  intro f hf
  refine ⟨ho f hf,?_⟩
  intro hfe
  have hfe' : f = e := Set.mem_singleton_iff.mp hfe
  subst f
  apply he
  rw [←hmap]
  exact List.mem_map_of_mem hf

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem counted_terminal_outside (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V)
    (hc : corridorCounted G w.retained w.blockers D ω x y) : x ∉ w.interior ∧ y ∉ w.interior := by
  have hleft (x y : V) (hc : corridorCounted G w.retained w.blockers D ω x y) : x ∉ w.interior := by
    intro hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxs : x ∈ w.path.support := List.mem_toFinset.mp hx'.1
    have hxne : x ≠ w.base ∧ x ≠ w.endpoint := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hx'.2
    have hxu := hxne.1
    have hxv := hxne.2
    obtain ⟨a,b,hab,ha,hb⟩ := path_internal_two_neighbors w.path w.path_isPath hxs hxu hxv
    obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc.1
    let qp := q.bypass
    have hqp : qp.IsPath := q.bypass_isPath
    obtain ⟨e,he,hGe⟩ := w.edge_has_label _ ha
    obtain ⟨f,hf,hGf⟩ := w.edge_has_label _ hb
    have hea := pivotal_image_mem_edges G _ qp e (hc.2.1 e he).2
    have heb := pivotal_image_mem_edges G _ qp f (hc.2.1 f hf).2
    rw [hGe] at hea
    rw [hGf] at heb
    exact hab ((hqp.eq_snd_of_mem_edges hea).trans (hqp.eq_snd_of_mem_edges heb).symm)
  exact ⟨hleft x y hc,hleft y x ((corridorCounted_symm G _ _ D ω x y).mp hc)⟩

end RawCorridor
end CorridorTerminalGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section CorridorIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_inter_const (S : Set E) : Measurable (fun ω : Set E => ω ∩ S) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  exact ((measurable_pi_apply e).comp MeasurableEquiv.setOfPred.symm.measurable).and measurable_const

 
theorem restriction_events_independent (p : unitInterval) (S T : Set E)
    (hST : Disjoint S T) (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (law p) ((fun ω => ω ∩ S) ⁻¹' A ∩ (fun ω => ω ∩ T) ⁻¹' B) =
      (law p) ((fun ω => ω ∩ S) ⁻¹' A) * (law p) ((fun ω => ω ∩ T) ⁻¹' B) := by
  let μ : Measure (E → Prop) := Measure.infinitePi (fun _ => bitLaw p)
  let σ : E → MeasurableSpace (E → Prop) := fun e =>
    MeasurableSpace.comap (fun f : E → Prop => f e) inferInstance
  have hi : iIndep σ μ := iIndepFun_infinitePi (X := fun (_ : E) (b : Prop) => b)
    (fun _ => measurable_id)
  have hle (e : E) : σ e ≤ (inferInstance : MeasurableSpace (E → Prop)) :=
    (measurable_pi_apply e).comap_le
  have hr (S : Set E) : @Measurable (E → Prop) (Set E) (⨆ e ∈ S, σ e) inferInstance
      (fun f => {e | f e} ∩ S) := by
    let : MeasurableSpace (E → Prop) := ⨆ e ∈ S, σ e
    apply measurable_setOfPred.comp
    apply Measurable.of_eval
    intro e
    change @Measurable (E → Prop) Prop (⨆ e ∈ S, σ e) inferInstance (fun f => f e ∧ e ∈ S)
    by_cases he : e ∈ S
    · have hm : @Measurable (E → Prop) Prop (⨆ e ∈ S, σ e) inferInstance (fun f => f e) :=
        Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
      simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,he,and_true] using hm
    · simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,he,and_false] using
        (measurable_const : @Measurable (E → Prop) Prop (⨆ e ∈ S, σ e) inferInstance (fun _ => False))
  have hm : (law p : Measure (Set E)) = μ.map (fun f => {e | f e}) := by
    simp only [law,setBernoulli_eq_map,Set.mem_univ,μ,bitLaw,bernoulliMeasure_def]
  rw [hm,Measure.map_apply measurable_setOfPred ((hA.preimage (measurable_inter_const S)).inter
    (hB.preimage (measurable_inter_const T))),
    Measure.map_apply measurable_setOfPred (hA.preimage (measurable_inter_const S)),
    Measure.map_apply measurable_setOfPred (hB.preimage (measurable_inter_const T))]
  exact (Indep_iff _ _ _).mp (indep_iSup_of_disjoint hle hi hST) _ _
    (hA.preimage (hr S)) (hB.preimage (hr T))

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem calibration_restriction (w : RawCorridor G k) (ω : Set E) :
    ω ∈ w.calibrationEvent ↔ ω ∩ (w.retained ∪ w.blockers) ∈ w.calibrationEvent := by
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨fun e he => ⟨ha he,Or.inl he⟩,hb.mono_right Set.inter_subset_left⟩
  · rintro ⟨ha,hb⟩
    refine ⟨fun e he => (ha he).1,Set.disjoint_left.mpr ?_⟩
    intro e he hw
    exact Set.disjoint_left.mp hb he ⟨hw,Or.inr he⟩

 

theorem calibration_independent (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) (p : unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (law p) (w.calibrationEvent ∩ (fun ω => ω ∩ internalEdges G (w.interior : Set V)ᶜ) ⁻¹' A) =
      (law p) w.calibrationEvent *
        (law p) ((fun ω => ω ∩ internalEdges G (w.interior : Set V)ᶜ) ⁻¹' A) := by
  have hQ : MeasurableSet w.calibrationEvent := by
    rw [w.calibrationEvent_eq hG hloc]
    apply measurableSet_edgePattern
    apply Finset.disjoint_left.mpr
    intro e he hb
    exact Set.disjoint_left.mp w.retained_disjoint_blockers
      ((w.retained_finite hG).mem_toFinset.mp he) ((w.blockers_finite hloc).mem_toFinset.mp hb)
  have heq : (fun ω => ω ∩ (w.retained ∪ w.blockers)) ⁻¹' w.calibrationEvent = w.calibrationEvent := by
    ext ω; exact (w.calibration_restriction ω).symm
  have hh := restriction_events_independent p _ _ (w.specified_disjoint_exterior hlen)
    w.calibrationEvent A hQ hA
  simpa only [heq] using hh

end RawCorridor
end CorridorIndependence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorContraction
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_union_attachment (G : BondGraph V E) (S T : Set E) (A : Set V)
    (hclosed : ∀ a b, a ∈ A → Conn G S a b → b ∈ A)
    (hT : ∀ e ∈ T, ∀ z ∈ G e, z ∈ A) {x y : V} (hc : Conn G (S ∪ T) x y) :
    Conn G S x y ∨ x ∈ A ∧ y ∈ A := by
  induction hc with
  | refl => exact Or.inl (conn_refl G S x)
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    rcases he with he | he
    · have hab : Conn G S a b := Relation.ReflTransGen.single ⟨e,he,heq⟩
      exact ih.elim (fun h => Or.inl (conn_trans G S h hab))
        (fun h => Or.inr ⟨h.1,hclosed a b h.2 hab⟩)
    · have ha := hT e he a (heq.symm ▸ (by simp : a ∈ s(a,b)))
      have hb := hT e he b (heq.symm ▸ (by simp : b ∈ s(a,b)))
      exact Or.inr ⟨ih.elim (fun h => hclosed a x ha (conn_symm G S h)) And.left,hb⟩

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def exterior (w : RawCorridor G k) (ω : Set E) : Set E :=
  ω ∩ internalEdges G (w.interior : Set V)ᶜ

def attachment (w : RawCorridor G k) (ω : Set E) : Set V :=
  {z | z ∈ w.path.support ∨ Conn G (w.exterior ω) w.base z ∨ Conn G (w.exterior ω) w.endpoint z}

theorem support_exterior_ports (w : RawCorridor G k) {z : V}
    (hz : z ∈ w.path.support) (ho : z ∉ w.interior) : z = w.base ∨ z = w.endpoint := by
  simpa only [interior,Finset.mem_sdiff,List.mem_toFinset,hz,true_and,
    Finset.mem_insert,Finset.mem_singleton,not_not] using ho

theorem attachment_closed (w : RawCorridor G k) (ω : Set E) (a b : V)
    (ha : a ∈ w.attachment ω) (hc : Conn G (w.exterior ω) a b) : b ∈ w.attachment ω := by
  rcases ha with ha | ha | ha
  · rcases conn_internal_eq_or_mem G (w.interior : Set V)ᶜ hc with rfl | ho
    · exact Or.inl ha
    · rcases w.support_exterior_ports ha ho.1 with rfl | rfl
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
  · exact Or.inr (Or.inl (conn_trans G _ ha hc))
  · exact Or.inr (Or.inr (conn_trans G _ ha hc))

theorem open_subset_exterior_retained (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) : ω ⊆ w.exterior ω ∪ w.retained := by
  intro e he
  by_cases hr : e ∈ w.retained
  · exact Or.inr hr
  · left
    refine ⟨he,?_⟩
    intro z hz hi
    exact Set.disjoint_left.mp hq.2 ⟨⟨z,hi,hz⟩,hr⟩ he

theorem connection_exterior_or_attachment (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) {x y : V} (hc : Conn G ω x y) :
    Conn G (w.exterior ω) x y ∨ x ∈ w.attachment ω ∧ y ∈ w.attachment ω := by
  apply conn_union_attachment G _ w.retained (w.attachment ω) (w.attachment_closed ω)
    (fun e he z hz => Or.inl (SimpleGraph.Walk.mem_support_of_mem_edges he hz))
  exact conn_mono G (w.open_subset_exterior_retained ω hq) hc

theorem attachment_outside (w : RawCorridor G k) (ω : Set E) {z : V}
    (ha : z ∈ w.attachment ω) (hz : z ∉ w.interior) :
    Conn G (w.exterior ω) w.base z ∨ Conn G (w.exterior ω) w.endpoint z := by
  rcases ha with ha | ha | ha
  · rcases w.support_exterior_ports ha hz with rfl | rfl
    · exact Or.inl (conn_refl G _ _)
    · exact Or.inr (conn_refl G _ _)
  · exact Or.inl ha
  · exact Or.inr ha

 
theorem counted_exterior_orientation (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (ω : Set E) (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hc : corridorCounted G w.retained w.blockers Set.univ ω x y) :
    ¬Conn G (w.exterior ω) w.base w.endpoint ∧
      ((Conn G (w.exterior ω) w.base x ∧ Conn G (w.exterior ω) w.endpoint y) ∨
       (Conn G (w.exterior ω) w.endpoint x ∧ Conn G (w.exterior ω) w.base y)) := by
  have hi : internalEdges G Set.univ = Set.univ := Set.eq_univ_of_forall (fun _ _ _ => trivial)
  have hc' : Conn G ω x y := by simpa only [hi,Set.inter_univ] using hc.1
  have hs : w.retained.Nonempty := by
    have hp : w.path.edges ≠ [] := by
      intro he
      have hh := congrArg List.length he
      simp only [SimpleGraph.Walk.length_edges,List.length_nil] at hh
      omega
    obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ hp
    obtain ⟨e,he,_⟩ := w.edge_has_label s hs
    exact ⟨e,he⟩
  have hnot : ¬Conn G (w.exterior ω) x y := by
    intro h
    obtain ⟨e,he⟩ := hs
    apply (hc.2.1 e he).2
    apply conn_mono G ?_ h
    intro f hf
    refine ⟨?_,?_⟩
    · simpa only [hi,Set.inter_univ] using hf.1
    · intro hfe
      have hfe' := Set.mem_singleton_iff.mp hfe
      subst f
      exact Set.disjoint_left.mp (w.specified_disjoint_exterior hlen) (Or.inl he) hf.2
  have hatt := (w.connection_exterior_or_attachment ω hq hc').resolve_left hnot
  have hout := w.counted_terminal_outside Set.univ ω x y hc
  have hx := w.attachment_outside ω hatt.1 hout.1
  have hy := w.attachment_outside ω hatt.2 hout.2
  have hne : ¬Conn G (w.exterior ω) w.base w.endpoint := by
    intro h
    apply hnot
    have hx' : Conn G (w.exterior ω) w.base x := hx.elim id (conn_trans G _ h)
    have hy' : Conn G (w.exterior ω) w.base y := hy.elim id (conn_trans G _ h)
    exact conn_trans G _ (conn_symm G _ hx') hy'
  refine ⟨hne,?_⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hnot (conn_trans G _ (conn_symm G _ hx) hy)).elim
  · exact Or.inl ⟨hx,hy⟩
  · exact Or.inr ⟨hx,hy⟩
  · exact (hnot (conn_trans G _ (conn_symm G _ hx) hy)).elim

end RawCorridor
end CorridorContraction
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CorridorBKCalibration
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

def exteriorOrientations (w : RawCorridor G k) (x y : V) : Set (Set E) :=
  orientedPivotalEvent G x y w.base w.endpoint ∪ orientedPivotalEvent G x y w.endpoint w.base

theorem measurableSet_exteriorOrientations (w : RawCorridor G k) (x y : V) :
    MeasurableSet (w.exteriorOrientations x y) :=
  (measurableSet_orientedPivotalEvent G x y w.base w.endpoint).union
    (measurableSet_orientedPivotalEvent G x y w.endpoint w.base)

omit [Countable V] [Countable E] in
theorem counted_subset_calibration_exterior (w : RawCorridor G k)
    (hlen : 3 ≤ w.path.length) (x y : V) :
    {ω | corridorCounted G w.retained w.blockers Set.univ ω x y} ⊆
      w.calibrationEvent ∩ (w.exterior ⁻¹' w.exteriorOrientations x y) := by
  intro ω hc
  have hi : internalEdges G Set.univ = Set.univ := Set.eq_univ_of_forall (fun _ _ _ => trivial)
  have hq : ω ∈ w.calibrationEvent := by
    refine ⟨fun e he => ?_,?_⟩
    · simpa only [hi,Set.inter_univ] using (hc.2.1 e he).1
    · simpa only [hi,Set.inter_univ] using hc.2.2
  refine ⟨hq,?_⟩
  obtain ⟨hne,ho⟩ := w.counted_exterior_orientation hlen ω hq x y hc
  rcases ho with ho | ho
  · exact Or.inl ⟨conn_symm G _ ho.1,ho.2,hne⟩
  · exact Or.inr ⟨conn_symm G _ ho.1,ho.2,fun h => hne (conn_symm G _ h)⟩

omit [Countable V] in
theorem exterior_orientation_BK (w : RawCorridor G k) (p : unitInterval) (x y a b : V) :
    (law p).real (w.exterior ⁻¹' orientedPivotalEvent G x y a b) ≤
      twoPoint G p x a * twoPoint G p b y := by
  apply le_trans (measureReal_mono ?_) (bk p {ω | Conn G ω x a} {ω | Conn G ω b y}
    (fun _ _ h hc => conn_mono G h hc) (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x a) (finiteWitness_conn G b y))
  intro ω h
  exact disjointOccurrence_upper _ _ Set.inter_subset_left
    (orientedPivotalEvent_subset_disjoint G x y a b h)

 

theorem counted_weight_bound (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) (x y : V) :
    w.weight P p * (law p).real {ω | corridorCounted G w.retained w.blockers Set.univ ω x y} ≤
      w.probability P * (twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y) := by
  have hi := w.calibration_independent hG hloc hlen p (w.exteriorOrientations x y)
    (w.measurableSet_exteriorOrientations x y)
  have hir : (law p).real (w.calibrationEvent ∩ w.exterior ⁻¹' w.exteriorOrientations x y) =
      (law p).real w.calibrationEvent * (law p).real (w.exterior ⁻¹' w.exteriorOrientations x y) := by
    exact congrArg ENNReal.toReal hi |>.trans ENNReal.toReal_mul
  have hb : (law p).real (w.exterior ⁻¹' w.exteriorOrientations x y) ≤
      twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y := by
    apply le_trans (measureReal_union_le _ _)
    exact add_le_add (w.exterior_orientation_BK p x y w.base w.endpoint)
      (w.exterior_orientation_BK p x y w.endpoint w.base)
  calc
    _ ≤ w.weight P p * (law p).real (w.calibrationEvent ∩ w.exterior ⁻¹' w.exteriorOrientations x y) :=
      mul_le_mul_of_nonneg_left (measureReal_mono (w.counted_subset_calibration_exterior hlen x y))
        (w.weight_nonneg P hP p)
    _ = w.probability P * (law p).real (w.exterior ⁻¹' w.exteriorOrientations x y) := by
      rw [hir,←mul_assoc,w.calibration_identity hG hloc P p hp hp₁]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (w.2.2.mass_nonneg P hP)

end RawCorridor
end CorridorBKCalibration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathIntegration
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev RawFrom (H : SimpleGraph V) (k : ℕ) (x : V) := Σ y : V, HoldingWalk H k x y

namespace RawFrom
variable {H : SimpleGraph V}

def zeroEquiv (x : V) : RawFrom H 0 x ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨x,.nil x⟩
  left_inv w := by rcases w with ⟨y,w⟩; cases w; rfl
  right_inv _ := rfl

def succEquiv (k : ℕ) (x : V) : RawFrom H (k+1) x ≃
    RawFrom H k x ⊕ (Σ z : H.neighborSet x, RawFrom H k z.val) where
  toFun
    | ⟨y,.hold w⟩ => .inl ⟨y,w⟩
    | ⟨y,.step (z := z) h w⟩ => .inr ⟨⟨z,h⟩,y,w⟩
  invFun
    | .inl ⟨y,w⟩ => ⟨y,.hold w⟩
    | .inr ⟨⟨z,h⟩,y,w⟩ => ⟨y,.step h w⟩
  left_inv w := by rcases w with ⟨y,w⟩; cases w <;> rfl
  right_inv w := by rcases w with ⟨y,w⟩ | ⟨⟨z,h⟩,y,w⟩ <;> rfl

instance finite [∀ x, Finite (H.neighborSet x)] (k : ℕ) (x : V) : Finite (RawFrom H k x) := by
  induction k generalizing x with
  | zero => exact Finite.of_equiv Unit (zeroEquiv x).symm
  | succ k ih =>
    let (z : V) : Finite (RawFrom H k z) := ih z
    exact Finite.of_equiv _ (succEquiv k x).symm

noncomputable def integral (P : V → V → ℝ) (k : ℕ) (x : V) (f : V → ℝ) : ℝ :=
  ∑' w : RawFrom H k x, w.2.mass P * f w.1

theorem integral_zero (P : V → V → ℝ) (x : V) (f : V → ℝ) :
    integral (H := H) P 0 x f = f x := by
  unfold integral
  rw [←(zeroEquiv x).symm.tsum_eq]
  simp only [zeroEquiv,Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,one_mul,tsum_fintype,Fintype.sum_unique]

theorem integral_succ [∀ x, Finite (H.neighborSet x)] (P : V → V → ℝ)
    (k : ℕ) (x : V) (f : V → ℝ) :
    integral (H := H) P (k+1) x f =
      P x x * integral (H := H) P k x f +
        ∑' z : H.neighborSet x, P x z * integral (H := H) P k z f := by
  unfold integral
  rw [←(succEquiv k x).symm.tsum_eq]
  let := Fintype.ofFinite (RawFrom H k x)
  let := Fintype.ofFinite (H.neighborSet x)
  let (z : H.neighborSet x) := Fintype.ofFinite (RawFrom H k z)
  simp only [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_sigma,succEquiv,
    Equiv.symm_mk,Equiv.coe_fn_mk,HoldingWalk.mass,mul_assoc,Finset.mul_sum]

end RawFrom

theorem finite_openSimpleGraph_neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Finite ((openSimpleGraph G Set.univ).neighborSet x) := by
  apply Set.Finite.to_subtype
  apply (finite_neighbors hloc x).subset
  intro y hy
  obtain ⟨_,e,_,he⟩ := hy
  exact ⟨e,he⟩

end RawPathIntegration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawPathOperator
attribute [local instance] Classical.propDecidable Classical.decEq

 theorem sum_step_decomposition (H : SimpleGraph V) (P : V → V → ℝ)
    (hs : ∀ x, (Function.support (P x)).Finite)
    (hstep : ∀ x y, x ≠ y → ¬H.Adj x y → P x y = 0) (x : V) (f : V → ℝ) :
    (∑' y, P x y * f y) = P x x * f x + ∑' y : H.neighborSet x, P x y * f y := by
  rw [(finiteKernel_summable_mul P hs x f).tsum_eq_add_tsum_ite x]
  congr 1
  have he : (∑' y : H.neighborSet x, if (y:V) = x then (0:ℝ) else P x y * f y) =
      ∑' y, if y = x then (0:ℝ) else P x y * f y := by
    apply tsum_subtype_eq_of_support_subset (f := fun y : V => if y = x then (0:ℝ) else P x y * f y)
    intro y hy
    by_contra hn
    apply hy
    by_cases h : y = x
    · simp only [h,ite_true]
    · simp only [ite_eq_right h,hstep x y (Ne.symm h) hn,zero_mul]
  rw [←he]
  apply tsum_congr
  intro y
  have hn : (y:V) ≠ x := by
    intro h
    have hy : H.Adj x y := y.property
    rw [h] at hy
    exact H.loopless.irrefl x hy
  rw [ite_eq_right hn]

 theorem raw_integral_operator (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x : V) (f : V → ℝ) :
    RawFrom.integral (H := openSimpleGraph G Set.univ) (walkKernel G hloc a) k x f =
      ∑' y, (matrixCoeff (P^k) x y).re * f y := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) :=
    finite_openSimpleGraph_neighbors G hloc z
  have hs (x : V) : (Function.support (walkKernel G hloc a x)).Finite := by
    simpa only [pow_one,hP,Complex.ofReal_re] using walkPower_finite_support G hloc a P hpos hP 1 x
  have hsP (x : V) : (Function.support (fun y => (matrixCoeff P x y).re)).Finite := by
    simpa only [hP,Complex.ofReal_re] using hs x
  induction k generalizing x with
  | zero => rw [RawFrom.integral_zero,pow_zero,positive_identity_action]
  | succ k ih =>
    rw [RawFrom.integral_succ,pow_succ',finite_positive_product_action P (P^k) hpos hsP
      (finite_positive_pow_support P hpos hsP k)]
    simp only [hP,Complex.ofReal_re]
    rw [sum_step_decomposition (openSimpleGraph G Set.univ) (walkKernel G hloc a) hs]
    · simp only [ih]
    · intro u v huv hn
      apply walkKernel_zero_of_not_step G hloc a u v huv
      intro ha
      apply hn
      obtain ⟨e,he⟩ := ha
      exact ⟨huv,e,Set.mem_univ e,he⟩

end RawPathOperator
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CorridorSum
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

def counted (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) : Prop :=
  3 ≤ w.path.length ∧ (∀ z ∈ w.path.support, z ∈ D) ∧
    corridorCounted G w.retained w.blockers D ω x y

theorem counted_iff (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    w.counted D ω x y ↔ 3 ≤ w.path.length ∧ corridorCounted G w.retained w.blockers D ω x y := by
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · rintro ⟨hlen,hc⟩
    exact ⟨hlen,w.support_subset_of_retained (by omega) D (fun e he => (hc.2.1 e he).1.2),hc⟩

theorem counted_base_mem_walk (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V)
    (hc : w.counted D ω x y) (q : (openSimpleGraph G (ω ∩ internalEdges G D)).Walk x y) :
    w.base ∈ q.support := by
  have hl : 0 < w.path.length := by have := hc.1; omega
  obtain ⟨s,hs,hbs⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hl)).mp w.path.start_mem_support
  obtain ⟨e,he,hGe⟩ := w.edge_has_label s hs
  have heq := pivotal_image_mem_edges G _ q e (hc.2.2.2.1 e he).2
  exact SimpleGraph.Walk.mem_support_of_mem_edges heq (hGe.symm ▸ hbs)

theorem counted_symm (w : RawCorridor G k) (D : Set V) (ω : Set E) (x y : V) :
    w.counted D ω x y ↔ w.counted D ω y x := by
  rw [counted_iff,counted_iff,corridorCounted_symm]

theorem measurableSet_counted [Countable E] (w : RawCorridor G k) (D : Set V) (x y : V) :
    MeasurableSet {ω | w.counted D ω x y} := by
  simp_rw [w.counted_iff]
  by_cases h : 3 ≤ w.path.length
  · simpa only [h,true_and] using measurableSet_corridorCounted G w.retained w.blockers D x y
  · simp only [h,false_and,Set.ofPred_false]; exact MeasurableSet.empty

end RawCorridor

 theorem finite_corridors_on_bases (G : BondGraph V E) (hloc : LocallyFinite G) (k : ℕ)
    (S : Set V) (hS : S.Finite) : {w : RawCorridor G k | w.base ∈ S}.Finite := by
  let (x : V) : Finite ((openSimpleGraph G Set.univ).neighborSet x) :=
    finite_openSimpleGraph_neighbors G hloc x
  let : Finite S := hS.to_subtype
  let f : (Σ x : S, RawFrom (openSimpleGraph G Set.univ) k x.val) → RawCorridor G k :=
    fun w => ⟨w.1.val,w.2⟩
  have hr : {w : RawCorridor G k | w.base ∈ S} = Set.range f := by
    ext w
    constructor
    · intro hw
      exact ⟨⟨⟨w.base,hw⟩,w.2⟩,rfl⟩
    · rintro ⟨w,rfl⟩
      exact w.1.property
  rw [hr]
  exact Set.finite_range f

 

theorem finite_counted_corridors (G : BondGraph V E) (hloc : LocallyFinite G) (k : ℕ)
    (D : Set V) (ω : Set E) (x y : V) : {w : RawCorridor G k | w.counted D ω x y}.Finite := by
  by_cases hc : Conn G (ω ∩ internalEdges G D) x y
  · obtain ⟨q⟩ := (conn_iff_reachable G _ x y).mp hc
    apply (finite_corridors_on_bases G hloc k {z | z ∈ q.support} (List.finite_toSet _)).subset
    exact fun w hw => w.counted_base_mem_walk D ω x y hw q
  · have he : {w : RawCorridor G k | w.counted D ω x y} = ∅ := by
      ext w
      exact ⟨fun h => hc h.2.2.1,False.elim⟩
    rw [he]
    exact Set.finite_empty

end CorridorSum
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualCorridorPenalty
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def corridorPenaltyTerm (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    {k : ℕ} (D : Set V) (ω : Set E) (x y : V) (w : RawCorridor G k) : ℝ :=
  if w.counted D ω x y then w.weight P p else 0

noncomputable def corridorPenalty (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) : ℝ :=
  ∑' w : RawCorridor G k, corridorPenaltyTerm G P p D ω x y w

theorem corridorPenaltyTerm_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) {k : ℕ} (D : Set V)
    (ω : Set E) (x y : V) (w : RawCorridor G k) :
    0 ≤ corridorPenaltyTerm G P p D ω x y w := by
  unfold corridorPenaltyTerm
  split_ifs
  · exact w.weight_nonneg P hP p
  · exact le_rfl

theorem corridorPenalty_finite_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    (Function.support (corridorPenaltyTerm G P p (k := k) D ω x y)).Finite := by
  apply (finite_counted_corridors G hloc k D ω x y).subset
  intro w hw
  by_contra hn
  exact hw (ite_eq_right hn)

theorem corridorPenalty_summable (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    Summable (corridorPenaltyTerm G P p (k := k) D ω x y) :=
  summable_of_hasFiniteSupport (corridorPenalty_finite_support G hloc P p k D ω x y)

theorem corridorPenalty_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (D : Set V)
    (ω : Set E) (x y : V) : 0 ≤ corridorPenalty G P p k D ω x y :=
  tsum_nonneg (corridorPenaltyTerm_nonneg G P hP p D ω x y)

theorem corridorPenalty_symm (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    corridorPenalty G P p k D ω x y = corridorPenalty G P p k D ω y x := by
  unfold corridorPenalty
  apply tsum_congr
  intro w
  simp only [corridorPenaltyTerm,w.counted_symm D ω x y]

theorem corridorPenalty_restrict (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    {D D' : Set V} {ω ω' : Set E} (hD : D ⊆ D') (hω : ω ⊆ ω')
    (x y : V) (hc : Conn G (ω ∩ internalEdges G D) x y) :
    corridorPenalty G P p k D' ω' x y ≤ corridorPenalty G P p k D ω x y := by
  apply (corridorPenalty_summable G hloc P p k D' ω' x y).tsum_le_tsum ?_
    (corridorPenalty_summable G hloc P p k D ω x y)
  intro w
  by_cases hn : w.counted D' ω' x y
  · have ho : w.counted D ω x y := (w.counted_iff D ω x y).mpr
      ⟨hn.1,corridorCounted_restrict G _ _ hD hω x y hc hn.2.2⟩
    simp only [corridorPenaltyTerm,hn,ho,ite_true,le_refl]
  · simpa only [corridorPenaltyTerm,hn,ite_false] using corridorPenaltyTerm_nonneg G P hP p D ω x y w

theorem measurable_corridorPenaltyTerm [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) {k : ℕ} (D : Set V) (x y : V) (w : RawCorridor G k) :
    Measurable (fun ω => corridorPenaltyTerm G P p D ω x y w) := by
  exact Measurable.ite (w.measurableSet_counted D x y) measurable_const measurable_const

theorem measurable_corridorPenalty [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (D : Set V) (x y : V) :
    Measurable (fun ω => corridorPenalty G P p k D ω x y) := by
  exact Measurable.tsum (fun w => measurable_corridorPenaltyTerm G P p D x y w)

end ActualCorridorPenalty
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ActualWeightedConnections
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def deformedConnection (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) : ℝ :=
  if x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y then
    Real.exp (-t * corridorPenalty G P p k D ω x y) else 0

noncomputable def deformedKernel (G : BondGraph V E) (P : V → V → ℝ) (p : unitInterval)
    (k : ℕ) (t : ℝ) (D : Set V) (x y : V) : ℝ :=
  ∫ ω, deformedConnection G P p k t D ω x y ∂law p

theorem deformedConnection_nonneg (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    0 ≤ deformedConnection G P p k t D ω x y := by
  unfold deformedConnection
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem deformedConnection_le_one (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x y : V) : deformedConnection G P p k t D ω x y ≤ 1 := by
  unfold deformedConnection
  split_ifs
  · apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (corridorPenalty_nonneg G P hP p k D ω x y)
  · exact zero_le_one

theorem deformedConnection_symm (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t D ω x y = deformedConnection G P p k t D ω y x := by
  have hc : Conn G (ω ∩ internalEdges G D) x y ↔ Conn G (ω ∩ internalEdges G D) y x :=
    ⟨conn_symm G _,conn_symm G _⟩
  simp only [deformedConnection,corridorPenalty_symm G P p k D ω x y,hc]
  congr 1
  apply propext; tauto

theorem deformedConnection_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) {D D' : Set V} {ω ω' : Set E} (hD : D ⊆ D') (hω : ω ⊆ ω')
    (x y : V) : deformedConnection G P p k t D ω x y ≤ deformedConnection G P p k t D' ω' x y := by
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · have hc' : x ∈ D' ∧ y ∈ D' ∧ Conn G (ω' ∩ internalEdges G D') x y :=
      ⟨hD hc.1,hD hc.2.1,conn_mono G (Set.inter_subset_inter hω (internalEdges_mono G hD)) hc.2.2⟩
    simp only [deformedConnection,hc,hc']
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (corridorPenalty_restrict G hloc P hP p k hD hω x y hc.2.2)
      (neg_nonpos.mpr ht)
  · simpa only [deformedConnection,hc,ite_false] using deformedConnection_nonneg G P p k t D' ω' x y

theorem measurable_deformedConnection [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : ℝ) (k : ℕ) (t : ℝ)
    (D : Set V) (x y : V) : Measurable (fun ω => deformedConnection G P p k t D ω x y) := by
  have hs : MeasurableSet {ω : Set E | x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y} := by
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
    · simpa only [hx,hy,true_and] using measurableSet_restrictedConn G (internalEdges G D) x y
    all_goals simp only [hx,hy,false_and,and_false,Set.ofPred_false]; exact MeasurableSet.empty
  exact Measurable.ite hs ((measurable_corridorPenalty G P p k D x y).const_mul (-t)).exp measurable_const

theorem integrable_deformedConnection [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    Integrable (fun ω => deformedConnection G P p k t D ω x y) (law p) := by
  apply Integrable.mono' (integrable_const (1:ℝ)) (measurable_deformedConnection G P p k t D x y).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (deformedConnection_nonneg G P p k t D ω x y)]
  exact deformedConnection_le_one G P hP p k t ht D ω x y

end ActualWeightedConnections
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedConnectionEndpoints
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenalty_diag (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x : V) : corridorPenalty G P p k D ω x x = 0 := by
  unfold corridorPenalty
  rw [←tsum_zero]
  apply tsum_congr
  intro w
  have hn : ¬w.counted D ω x x := by
    intro hc
    have hl : 0 < w.path.length := by have := hc.1; omega
    obtain ⟨s,hs,_⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
      (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hl)).mp w.path.start_mem_support
    obtain ⟨e,he,_⟩ := w.edge_has_label s hs
    exact (hc.2.2.2.1 e he).2 (conn_refl G _ x)
  exact ite_eq_right hn

theorem deformedConnection_diag (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x : V) (hx : x ∈ D) :
    deformedConnection G P p k t D ω x x = 1 := by
  simp only [deformedConnection,hx,conn_refl G _ x,and_self,ite_true,
    corridorPenalty_diag,mul_zero,Real.exp_zero]

theorem deformedConnection_zero (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k 0 D ω x y =
      if x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y then 1 else 0 := by
  simp only [deformedConnection,neg_zero,zero_mul,Real.exp_zero]

theorem deformedConnection_full_zero (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ)
    (k : ℕ) (ω : Set E) (x y : V) : deformedConnection G P p k 0 Set.univ ω x y =
      if Conn G ω x y then 1 else 0 := by
  have hi : internalEdges G Set.univ = Set.univ := Set.eq_univ_of_forall (fun _ _ _ => trivial)
  simp only [deformedConnection_zero,Set.mem_univ,true_and,hi,Set.inter_univ]

theorem deformedConnection_change (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (D : Set V) (ω : Set E) (x y : V) :
    0 ≤ deformedConnection G P p k 0 D ω x y - deformedConnection G P p k t D ω x y ∧
    deformedConnection G P p k 0 D ω x y - deformedConnection G P p k t D ω x y ≤
      t*corridorPenalty G P p k D ω x y := by
  have hN := corridorPenalty_nonneg G P hP p k D ω x y
  by_cases hc : x ∈ D ∧ y ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y
  · simp only [deformedConnection,hc,ite_true,neg_zero,zero_mul,Real.exp_zero,and_self]
    constructor
    · exact sub_nonneg.mpr ((Real.exp_le_one_iff).mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hN))
    · have h := Real.one_sub_le_exp_neg (t*corridorPenalty G P p k D ω x y)
      rw [←neg_mul] at h
      linarith
  · simp only [deformedConnection,hc,ite_false,sub_self]
    exact ⟨le_rfl,mul_nonneg ht hN⟩

theorem deformedKernel_zero [Countable V] [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : unitInterval) (k : ℕ) (x y : V) :
    deformedKernel G P p k 0 Set.univ x y = twoPoint G p x y := by
  unfold deformedKernel
  simp_rw [deformedConnection_full_zero]
  have hi := integral_indicator_const (μ := law p) (1:ℝ) (measurableSet_conn G x y)
  simpa only [Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_one,Measure.real,twoPoint] using hi

end WeightedConnectionEndpoints
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkDiagrams
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem raw_diagram_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (k : ℕ) (x y : V) :
    HasSum (fun w : RawCorridor G k => w.probability (walkKernel G hloc a) *
      ((matrixCoeff A x w.base).re * (matrixCoeff A w.endpoint y).re))
      (matrixCoeff (A*(P^k*A)) x y).re := by
  let (z : V) : Finite ((openSimpleGraph G Set.univ).neighborSet z) :=
    finite_openSimpleGraph_neighbors G hloc z
  let F := fun w : RawCorridor G k => w.probability (walkKernel G hloc a) *
    ((matrixCoeff A x w.base).re * (matrixCoeff A w.endpoint y).re)
  have hFn (w : RawCorridor G k) : 0 ≤ F w :=
    mul_nonneg (w.2.2.mass_nonneg _ hK) (mul_nonneg (hA _ _).2 (hA _ _).2)
  have hr (z : V) : (∑' w : RawFrom (openSimpleGraph G Set.univ) k z, F ⟨z,w⟩) =
      (matrixCoeff A x z).re * (matrixCoeff (P^k*A) z y).re := by
    have h := raw_integral_operator G hloc a P hpos hP k z (fun u => (matrixCoeff A u y).re)
    have he : (∑' w : RawFrom (openSimpleGraph G Set.univ) k z, F ⟨z,w⟩) =
        (matrixCoeff A x z).re * RawFrom.integral (H := openSimpleGraph G Set.univ)
          (walkKernel G hloc a) k z (fun u => (matrixCoeff A u y).re) := by
      rw [RawFrom.integral,←tsum_mul_left]
      apply tsum_congr
      intro w
      dsimp only [F,RawCorridor.probability,RawCorridor.base,RawCorridor.endpoint]
      change w.2.mass _ * (_ * _) = _ * (w.2.mass _ * _)
      ring
    rw [he,h,((hpos.pow k).mul_hasSum A z y).tsum_eq]
  have ho := hA.mul_hasSum (P^k*A) x y
  have hs : Summable F := (summable_sigma_of_nonneg hFn).mpr ⟨fun z => by
    let := Fintype.ofFinite (RawFrom (openSimpleGraph G Set.univ) k z)
    exact (hasSum_fintype _).summable,by simpa only [hr] using ho.summable⟩
  have he : (∑' w, F w) = (matrixCoeff (A*(P^k*A)) x y).re := by
    rw [hs.tsum_sigma]
    simpa only [hr] using ho.tsum_eq
  exact he ▸ hs.hasSum

 theorem sandwich_selfAdjoint (A P : Hilbert V →L[ℂ] Hilbert V)
    (hA : IsSelfAdjoint A) (hP : IsSelfAdjoint P) (k : ℕ) : IsSelfAdjoint (A*(P^k*A)) := by
  change star (A*(P^k*A)) = A*(P^k*A)
  simp only [star_mul,hA.star_eq,(hP.pow k).star_eq,mul_assoc]

end RawWalkDiagrams
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RawWalkSymmetricDiagrams
attribute [local instance] Classical.propDecidable Classical.decEq

theorem raw_two_diagrams_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (hAs : IsSelfAdjoint A)
    (k : ℕ) (x y : V) :
    HasSum (fun w : RawCorridor G k => w.probability (walkKernel G hloc a) *
      ((matrixCoeff A x w.base).re * (matrixCoeff A w.endpoint y).re +
       (matrixCoeff A x w.endpoint).re * (matrixCoeff A w.base y).re))
      (2*(matrixCoeff (A*(P^k*A)) x y).re) := by
  have h₁ := raw_diagram_hasSum G hloc a P hpos hP hK A hA k x y
  have h₂ := raw_diagram_hasSum G hloc a P hpos hP hK A hA k y x
  have hh := h₁.add h₂
  have hC := matrixCoeff_real_symm (A*(P^k*A)) (sandwich_selfAdjoint A P hAs hPs k) y x
  rw [hC,←two_mul] at hh
  convert hh using 1
  ext w
  rw [matrixCoeff_real_symm A hAs y w.base,matrixCoeff_real_symm A hAs w.endpoint x]
  ring

end RawWalkSymmetricDiagrams
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section PenaltyTermExpectation
attribute [local instance] Classical.propDecidable Classical.decEq

 theorem integrable_corridorPenaltyTerm [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : unitInterval) {k : ℕ} (D : Set V) (x y : V) (w : RawCorridor G k) :
    Integrable (fun ω => corridorPenaltyTerm G P p D ω x y w) (law p) := by
  exact (integrable_const (w.weight P p)).indicator (w.measurableSet_counted D x y)

theorem integral_corridorPenaltyTerm [Countable E] (G : BondGraph V E)
    (P : V → V → ℝ) (p : unitInterval) {k : ℕ} (D : Set V) (x y : V) (w : RawCorridor G k) :
    (∫ ω, corridorPenaltyTerm G P p D ω x y w ∂law p) =
      w.weight P p * (law p).real {ω | w.counted D ω x y} := by
  have h := integral_indicator_const (μ := law p) (w.weight P p) (w.measurableSet_counted D x y)
  simpa only [corridorPenaltyTerm,Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_comm] using h

 
theorem integral_corridorPenaltyTerm_le [Countable V] [Countable E]
    (G : BondGraph V E) (hG : Function.Injective G) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) {k : ℕ} (x y : V) (w : RawCorridor G k) :
    (∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w ∂law p) ≤
      w.probability P * (twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y) := by
  rw [integral_corridorPenaltyTerm]
  by_cases hl : 3 ≤ w.path.length
  · have he : {ω | w.counted Set.univ ω x y} =
        {ω | corridorCounted G w.retained w.blockers Set.univ ω x y} := by
      ext ω
      simp only [Set.mem_ofPred_eq,w.counted_iff,hl,true_and]
    rw [he]
    exact w.counted_weight_bound hG hloc hl P hP p hp hp₁ x y
  · have he : {ω | w.counted Set.univ ω x y} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq,w.counted_iff,hl,false_and,Set.mem_empty_iff_false]
    rw [he,measureReal_empty,mul_zero]
    exact mul_nonneg (w.2.2.mass_nonneg P hP) (add_nonneg
      (mul_nonneg (twoPoint_nonneg G p x w.base) (twoPoint_nonneg G p w.endpoint y))
      (mul_nonneg (twoPoint_nonneg G p x w.endpoint) (twoPoint_nonneg G p w.base y)))

end PenaltyTermExpectation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FullCorridorPenaltyExpectation
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

theorem corridorPenalty_integrable_bound (G : BondGraph V E)
    (hG : Function.Injective G) (hloc : LocallyFinite G) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (hAs : IsSelfAdjoint A)
    (hAT : ∀ x y, matrixCoeff A x y = (twoPoint G p x y : ℂ)) (k : ℕ) (x y : V) :
    Integrable (fun ω => corridorPenalty G (walkKernel G hloc a) p k Set.univ ω x y) (law p) ∧
    (∫ ω, corridorPenalty G (walkKernel G hloc a) p k Set.univ ω x y ∂law p) ≤
      2*(matrixCoeff (A*(P^k*A)) x y).re := by
  let K := walkKernel G hloc a
  have hK (u v : V) : 0 ≤ K u v := by simpa only [hP,Complex.ofReal_re] using (hpos u v).2
  let F := fun w : RawCorridor G k => fun ω : Set E => corridorPenaltyTerm G K p Set.univ ω x y w
  have hFi (w : RawCorridor G k) : Integrable (F w) (law p) := integrable_corridorPenaltyTerm G K p Set.univ x y w
  have hFn (w : RawCorridor G k) (ω : Set E) : 0 ≤ F w ω := corridorPenaltyTerm_nonneg G K hK p _ ω x y w
  have hd := raw_two_diagrams_hasSum G hloc a P hpos hPs hP hK A hA hAs k x y
  simp only [hAT,Complex.ofReal_re] at hd
  have hb (w : RawCorridor G k) := integral_corridorPenaltyTerm_le G hG hloc K hK p hp hp₁ x y w
  have hs : Summable (fun w => ∫ ω, F w ω ∂law p) := Summable.of_nonneg_of_le
    (fun w => integral_nonneg (hFn w)) hb hd.summable
  have hsN (ω : Set E) := corridorPenalty_summable G hloc K p k Set.univ ω x y
  have hlin : (∫⁻ ω, ENNReal.ofReal (corridorPenalty G K p k Set.univ ω x y) ∂law p) =
      ENNReal.ofReal (∑' w, ∫ ω, F w ω ∂law p) := by
    have he (ω : Set E) : ENNReal.ofReal (corridorPenalty G K p k Set.univ ω x y) =
        ∑' w, ENNReal.ofReal (F w ω) := ENNReal.ofReal_tsum_of_nonneg (fun w => hFn w ω) (hsN ω)
    simp_rw [he]
    rw [lintegral_tsum (fun w => (hFi w).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [←ofReal_integral_eq_lintegral_ofReal (hFi _) (Filter.Eventually.of_forall (hFn _))]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun w => integral_nonneg (hFn w)) hs).symm
  have hNn (ω : Set E) := corridorPenalty_nonneg G K hK p k Set.univ ω x y
  have hi : Integrable (fun ω => corridorPenalty G K p k Set.univ ω x y) (law p) :=
    ⟨(measurable_corridorPenalty G K p k Set.univ x y).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hNn)).mpr (by rw [hlin]; exact ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  have hn : Summable (fun w => ∫ ω, ‖F w ω‖ ∂law p) := by
    simpa only [Real.norm_of_nonneg (hFn _ _)] using hs
  change (∫ ω, ∑' w, F w ω ∂law p) ≤ _
  rw [←integral_tsum_of_summable_integral_norm hFi hn]
  exact (hs.tsum_le_tsum hb hd.summable).trans_eq hd.tsum_eq

end FullCorridorPenaltyExpectation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SmallDeformationEntrywise
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

 

theorem deformedKernel_change_bound (G : BondGraph V E)
    (hG : Function.Injective G) (hloc : LocallyFinite G) (p : unitInterval)
    (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : PositiveRealMatrix A) (hAs : IsSelfAdjoint A)
    (hAT : ∀ x y, matrixCoeff A x y = (twoPoint G p x y : ℂ))
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (x y : V) :
    0 ≤ twoPoint G p x y - deformedKernel G (walkKernel G hloc a) p k t Set.univ x y ∧
    twoPoint G p x y - deformedKernel G (walkKernel G hloc a) p k t Set.univ x y ≤
      2*t*(matrixCoeff (A*(P^k*A)) x y).re := by
  let K := walkKernel G hloc a
  have hK (u v : V) : 0 ≤ K u v := by simpa only [hP,Complex.ofReal_re] using (hpos u v).2
  have hi₀ := integrable_deformedConnection G K hK p k 0 (le_refl _) Set.univ x y
  have hi := integrable_deformedConnection G K hK p k t ht Set.univ x y
  have he : twoPoint G p x y - deformedKernel G K p k t Set.univ x y =
      ∫ ω, deformedConnection G K p k 0 Set.univ ω x y - deformedConnection G K p k t Set.univ ω x y ∂law p := by
    rw [integral_sub hi₀ hi]
    change _ = deformedKernel G K p k 0 Set.univ x y - _
    rw [deformedKernel_zero]
    rfl
  rw [he]
  refine ⟨integral_nonneg (fun ω => (deformedConnection_change G K hK p k t ht Set.univ ω x y).1),?_⟩
  obtain ⟨hNi,hNb⟩ := corridorPenalty_integrable_bound G hG hloc p hp hp₁ a P hpos hPs hP A hA hAs hAT k x y
  calc
    _ ≤ ∫ ω, t*corridorPenalty G K p k Set.univ ω x y ∂law p :=
      integral_mono (hi₀.sub hi) (hNi.const_mul t)
        (fun ω => (deformedConnection_change G K hK p k t ht Set.univ ω x y).2)
    _ = t*∫ ω, corridorPenalty G K p k Set.univ ω x y ∂law p := integral_const_mul _ _
    _ ≤ t*(2*(matrixCoeff (A*(P^k*A)) x y).re) := mul_le_mul_of_nonneg_left hNb ht
    _ = _ := by ring

omit [Countable V] [Countable E] in
theorem deformedKernel_nonneg (G : BondGraph V E) (P : V → V → ℝ) (p : unitInterval)
    (k : ℕ) (t : ℝ) (D : Set V) (x y : V) : 0 ≤ deformedKernel G P p k t D x y :=
  integral_nonneg (fun ω => deformedConnection_nonneg G P p k t D ω x y)

end SmallDeformationEntrywise
end Percolation

end OAI
