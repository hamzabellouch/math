import OAI.Analysis.HenonEmden.LayerPressure

namespace OAI

universe uP uP2 uP3 uP4 uP5 uP6 uP7 uP8

section Endpoints

open Set MeasureTheory Filter Topology
open scoped ENNReal
open Classical
namespace HenonLaneEmden.LineComponents

/-- Relative endpoints are chosen by measurable rational exits. On the only
components whose weight is positive they are the genuine finite endpoints. -/
noncomputable def lowerEndpoint {P : Type uP} (U : Set (P × ℝ)) (p : P × ℝ) : ℝ :=
  p.2 - (backwardExit (relativeLayer U) p).toReal
noncomputable def upperEndpoint {P : Type uP2} (U : Set (P × ℝ)) (p : P × ℝ) : ℝ :=
  p.2 + (forwardExit (relativeLayer U) p).toReal

lemma measurable_lowerEndpoint {P : Type uP3} [TopologicalSpace P] [MeasurableSpace P]
    [BorelSpace P] {U : Set (P × ℝ)} (hU : IsOpen U) : Measurable (lowerEndpoint U) :=
  measurable_snd.sub (measurable_backwardExit (isOpen_relativeLayer hU)).ennreal_toReal
lemma measurable_upperEndpoint {P : Type uP4} [TopologicalSpace P] [MeasurableSpace P]
    [BorelSpace P] {U : Set (P × ℝ)} (hU : IsOpen U) : Measurable (upperEndpoint U) :=
  measurable_snd.add (measurable_forwardExit (isOpen_relativeLayer hU)).ennreal_toReal

lemma relative_component_eq_Ioo {P : Type uP5} [TopologicalSpace P]
    {U : Set (P × ℝ)} (hU : IsOpen U) {p : P × ℝ} (hp : p ∈ U)
    (hfin : componentLength (relativeLayer U) p ≠ ⊤) :
    connectedComponentIn {s | (p.1,s) ∈ U} p.2 =
      Ioo (lowerEndpoint U p) (upperEndpoint U p) := by
  have hp0 : (p,0) ∈ relativeLayer U := by simpa [relativeLayer] using hp
  have he := component_eq_Ioo (isOpen_relativeLayer hU) hp0
    (ENNReal.add_ne_top.mp hfin).1 (ENNReal.add_ne_top.mp hfin).2
  have him := image_relative_component (U := {s | (p.1,s) ∈ U}) (x := p.2) hp
  have hsets : {r : ℝ | (p,r) ∈ relativeLayer U} =
      {r : ℝ | (p.2,r) ∈ shiftedLayer {s | (p.1,s) ∈ U}} := rfl
  rw [hsets] at he
  rw [← him,he]
  ext s
  constructor
  · rintro ⟨r,hr,rfl⟩
    constructor <;> dsimp [lowerEndpoint,upperEndpoint] <;> linarith [hr.1,hr.2]
  · intro hs
    refine ⟨s-p.2,?_,by ring⟩
    constructor <;> dsimp [lowerEndpoint,upperEndpoint] at hs <;> linarith [hs.1,hs.2]

lemma relative_endpoints_eq {P : Type uP6} [TopologicalSpace P]
    {U : Set (P × ℝ)} (hU : IsOpen U) {p : P × ℝ} (hp : p ∈ U)
    (hfin : componentLength (relativeLayer U) p ≠ ⊤) :
    lowerEndpoint U p = sInf (connectedComponentIn {s | (p.1,s) ∈ U} p.2) ∧
    upperEndpoint U p = sSup (connectedComponentIn {s | (p.1,s) ∈ U} p.2) := by
  have he := relative_component_eq_Ioo hU hp hfin
  have hpI := mem_connectedComponentIn (F := {s | (p.1,s) ∈ U}) hp
  rw [he] at hpI
  rw [he,csInf_Ioo (lt_trans hpI.1 hpI.2),csSup_Ioo (lt_trans hpI.1 hpI.2)]
  exact ⟨rfl,rfl⟩

/-- Components are closed relative to the original set. -/
lemma closure_component_inter_subset {U : Set ℝ} {x : ℝ} (hx : x ∈ U) :
    closure (connectedComponentIn U x) ∩ U ⊆ connectedComponentIn U x := by
  intro y hy
  have hpre : IsPreconnected (insert y (connectedComponentIn U x)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset_iff.mpr ⟨hy.1,subset_closure⟩)
  have hsub := hpre.subset_connectedComponentIn
    (mem_insert_of_mem _ (mem_connectedComponentIn hx))
    (insert_subset_iff.mpr ⟨hy.2,connectedComponentIn_subset U x⟩)
  exact hsub (mem_insert _ _)

lemma component_endpoints_frontier {U : Set ℝ} {x a b : ℝ} (hx : x ∈ U)
    (he : connectedComponentIn U x = Ioo a b) : a ∈ frontier U ∧ b ∈ frontier U := by
  have hxI := mem_connectedComponentIn hx
  rw [he] at hxI
  have hab : a < b := lt_trans hxI.1 hxI.2
  have hac : a ∈ closure (connectedComponentIn U x) := by rw [he,closure_Ioo hab.ne]; exact ⟨le_rfl,hab.le⟩
  have hbc : b ∈ closure (connectedComponentIn U x) := by rw [he,closure_Ioo hab.ne]; exact ⟨hab.le,le_rfl⟩
  have haU : a ∉ U := by
    intro ha
    have hh := closure_component_inter_subset hx ⟨hac,ha⟩
    rw [he] at hh
    exact (lt_irrefl a) hh.1
  have hbU : b ∉ U := by
    intro hb
    have hh := closure_component_inter_subset hx ⟨hbc,hb⟩
    rw [he] at hh
    exact (lt_irrefl b) hh.2
  exact ⟨⟨closure_mono (connectedComponentIn_subset U x) hac,
      fun ha => haU (interior_subset ha)⟩,
    ⟨closure_mono (connectedComponentIn_subset U x) hbc,
      fun hb => hbU (interior_subset hb)⟩⟩

lemma value_eq_level_at_endpoint {f : ℝ → ℝ} {O : Set ℝ} {t x a b : ℝ}
    (hx : x ∈ {s | s ∈ O ∧ t < f s})
    (he : connectedComponentIn {s | s ∈ O ∧ t < f s} x = Ioo a b)
    {y : ℝ} (hy : y=a ∨ y=b) (hyO : y ∈ O) (hf : ContinuousAt f y) : f y = t := by
  have hfront := component_endpoints_frontier hx he
  have hyfront : y ∈ frontier {s | s ∈ O ∧ t < f s} := hy.elim (fun h => h ▸ hfront.1) (fun h => h ▸ hfront.2)
  have hxI := mem_connectedComponentIn hx
  rw [he] at hxI
  have hab : a < b := lt_trans hxI.1 hxI.2
  have hyc : y ∈ closure (connectedComponentIn {s | s ∈ O ∧ t < f s} x) := by
    rw [he,closure_Ioo hab.ne]
    rcases hy with rfl | rfl <;> exact ⟨by linarith,by linarith⟩
  have hynot : y ∉ {s | s ∈ O ∧ t < f s} := by
    intro h
    have hm := closure_component_inter_subset hx ⟨hyc,h⟩
    rw [he] at hm
    rcases hy with rfl | rfl <;> linarith [hm.1,hm.2]
  apply le_antisymm
  · exact le_of_not_gt (fun h => hynot ⟨hyO,h⟩)
  · have hmem := _root_.mem_closure_image hf hyc
    have hsub : f '' connectedComponentIn {s | s ∈ O ∧ t < f s} x ⊆ Ici t := by
      rintro _ ⟨s,hs,rfl⟩
      exact (connectedComponentIn_subset _ _ hs).2.le
    exact (closure_minimal hsub isClosed_Ici) hmem

lemma setWeight_le_on_closure {h d : ℝ → ℝ} {δ : ℝ} {I : Set ℝ}
    (hh : Continuous h) (hn : ∀ x ∈ I, 0 ≤ h x) {y : ℝ} (hy : y ∈ closure I) :
    (setWeight h d δ I).toReal ≤ h y := by
  have hs : I ⊆ {x | (setWeight h d δ I).toReal ≤ h x} := by
    intro x hx
    exact (ENNReal.toReal_le_toReal setWeight_ne_top ENNReal.ofReal_ne_top).mpr (setWeight_le hx)
      |>.trans_eq (ENNReal.toReal_ofReal (hn x hx))
  exact (closure_minimal hs (isClosed_le continuous_const hh)) hy

lemma endpoints_distance_bound {h d : ℝ → ℝ} {δ x a b : ℝ} {I : Set ℝ}
    (he : I = Ioo a b) (hx : x ∈ I) (hδ : 0 ≤ δ) (hd : 0 ≤ d x)
    (hw : 0 < (setWeight h d δ I).toReal) :
    |a-x| ≤ 2*δ*d x ∧ |b-x| ≤ 2*δ*d x := by
  have hxI : a < x ∧ x < b := by simpa [he] using hx
  have htest : I.Nonempty ∧ volume I ≠ ⊤ ∧ volume I ≤ ENNReal.ofReal (2*δ)*setInf d I := by
    unfold setWeight at hw
    split_ifs at hw with htest
    · exact htest
    · simp at hw
  have hv : volume I ≤ ENNReal.ofReal (2*δ)*ENNReal.ofReal (d x) := htest.2.2.trans (by
    gcongr
    exact setInf_le hx)
  rw [he,Real.volume_Ioo,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*δ)] at hv
  have hlen : b-a ≤ 2*δ*d x := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*δ*d x)).mp hv
  rw [abs_of_neg (by linarith : a-x<0),abs_of_pos (by linarith : 0<b-x)]
  constructor <;> linarith

lemma relative_componentLength_eq {P : Type uP7} [TopologicalSpace P]
    {U : Set (P × ℝ)} (hU : IsOpen U) {p : P × ℝ} (hp : p ∈ U) :
    componentLength (relativeLayer U) p =
      volume (connectedComponentIn {s | (p.1,s) ∈ U} p.2) := by
  have he := shifted_componentLength_eq (isOpen_section hU p.1) hp
  simpa only [componentLength,forwardExit,backwardExit,SegmentInside,relativeLayer,
    shiftedLayer,Set.mem_ofPred] using he

lemma relative_endpoints_eq_of_weight_pos {P : Type uP8} [TopologicalSpace P]
    {U : Set (P × ℝ)} (hU : IsOpen U) {p : P × ℝ} (hp : p ∈ U)
    {h d : ℝ → ℝ} {δ : ℝ}
    (hw : 0 < (setWeight h d δ (connectedComponentIn {s | (p.1,s) ∈ U} p.2)).toReal) :
    lowerEndpoint U p = sInf (connectedComponentIn {s | (p.1,s) ∈ U} p.2) ∧
    upperEndpoint U p = sSup (connectedComponentIn {s | (p.1,s) ∈ U} p.2) := by
  apply relative_endpoints_eq hU hp
  rw [relative_componentLength_eq hU hp]
  unfold setWeight at hw
  split_ifs at hw with hh
  · exact hh.2.1
  · simp at hw

end HenonLaneEmden.LineComponents
end Endpoints

end OAI
