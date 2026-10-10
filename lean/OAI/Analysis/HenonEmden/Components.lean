import OAI.Analysis.HenonEmden.CapContinuity

namespace OAI

universe uX

section Components
open MeasureTheory Set Filter Topology
open scoped ENNReal
open Classical
namespace HenonLaneEmden.LineComponents

variable {X : Type uX} [TopologicalSpace X]

/-- All points of the closed segment between the base point `0` and `r`
remain in the open line layer. -/
def SegmentInside (U : Set (X × ℝ)) (p : X) (r : ℝ) : Prop :=
  ∀ s ∈ uIcc 0 r, (p,s) ∈ U

omit [TopologicalSpace X] in
lemma segmentInside_iff_mem_component {U : Set (X × ℝ)} {p : X} {r : ℝ}
    (hp : (p,0) ∈ U) :
    SegmentInside U p r ↔ r ∈ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 := by
  constructor
  · intro h
    exact isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc h right_mem_uIcc
  · intro hr s hs
    have hp' : 0 ∈ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 := mem_connectedComponentIn hp
    exact connectedComponentIn_subset {s : ℝ | (p,s) ∈ U} 0
      (isPreconnected_connectedComponentIn.ordConnected.uIcc_subset hp' hr hs)

omit [TopologicalSpace X] in
lemma segmentInside_zero {U : Set (X × ℝ)} {p : X} :
    SegmentInside U p 0 ↔ (p,0) ∈ U := by simp [SegmentInside]

omit [TopologicalSpace X] in
lemma segmentInside_base {U : Set (X × ℝ)} {p : X} {r : ℝ}
    (h : SegmentInside U p r) : (p,0) ∈ U := h 0 left_mem_uIcc

omit [TopologicalSpace X] in
lemma segmentInside_endpoint {U : Set (X × ℝ)} {p : X} {r : ℝ}
    (h : SegmentInside U p r) : (p,r) ∈ U := h r right_mem_uIcc

lemma isOpen_segmentInside {U : Set (X × ℝ)} (hU : IsOpen U) (r : ℝ) :
    IsOpen {p : X | SegmentInside U p r} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hprod : ({p} : Set X) ×ˢ uIcc 0 r ⊆ U := by
    rintro ⟨q,s⟩ ⟨hq,hs⟩
    obtain rfl := mem_singleton_iff.mp hq
    exact hp s hs
  obtain ⟨V,W,hV,-,hpV,hsegW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hU hprod
  exact Filter.mem_of_superset (hV.mem_nhds (singleton_subset_iff.mp hpV))
    (fun q hq s hs => hVW ⟨hq,hsegW hs⟩)

lemma isOpen_section {U : Set (X × ℝ)} (hU : IsOpen U) (p : X) :
    IsOpen {s : ℝ | (p,s) ∈ U} := hU.preimage (continuous_const.prodMk continuous_id)

/-- The rational definition makes joint measurability independent of coordinates
on the direction-dependent transverse hyperplanes. -/
noncomputable def forwardExit (U : Set (X × ℝ)) (p : X) : ℝ≥0∞ :=
  ⨆ r : ℚ, if SegmentInside U p (r : ℝ) then ENNReal.ofReal (r : ℝ) else 0

noncomputable def backwardExit (U : Set (X × ℝ)) (p : X) : ℝ≥0∞ :=
  ⨆ r : ℚ, if SegmentInside U p (-(r : ℝ)) then ENNReal.ofReal (r : ℝ) else 0

noncomputable def componentLength (U : Set (X × ℝ)) (p : X) : ℝ≥0∞ :=
  forwardExit U p + backwardExit U p

noncomputable def componentInf (U : Set (X × ℝ)) (value : X × ℝ → ℝ) (p : X) : ℝ≥0∞ :=
  ⨅ r : ℚ, if SegmentInside U p (r : ℝ) then ENNReal.ofReal (value (p,(r : ℝ))) else ⊤

omit [TopologicalSpace X] in
lemma componentInf_le_base {U : Set (X × ℝ)} (value : X × ℝ → ℝ) {p : X}
    (hp : (p,0) ∈ U) : componentInf U value p ≤ ENNReal.ofReal (value (p,0)) := by
  have h := iInf_le (fun r : ℚ => if SegmentInside U p (r : ℝ)
    then ENNReal.ofReal (value (p,(r : ℝ))) else ⊤) 0
  simpa [componentInf, segmentInside_zero, hp] using h

omit [TopologicalSpace X] in
lemma componentInf_ne_top {U : Set (X × ℝ)} (value : X × ℝ → ℝ) {p : X}
    (hp : (p,0) ∈ U) : componentInf U value p ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (componentInf_le_base value hp)

noncomputable def componentWeight (U : Set (X × ℝ)) (h d : X × ℝ → ℝ)
    (δ : ℝ) (p : X) : ℝ≥0∞ :=
  if (p,0) ∈ U ∧ componentLength U p ≠ ⊤ ∧
      componentLength U p ≤ ENNReal.ofReal (2*δ) * componentInf U d p
  then componentInf U h p else 0

omit [TopologicalSpace X] in
lemma componentWeight_le_base {U : Set (X × ℝ)} (h d : X × ℝ → ℝ) (δ : ℝ) (p : X) :
    componentWeight U h d δ p ≤ ENNReal.ofReal (h (p,0)) := by
  unfold componentWeight
  split_ifs with hp
  · exact componentInf_le_base h hp.1
  · exact bot_le

/-- The rational infimum equals the infimum over the genuine open component. -/
lemma componentInf_eq_component {U : Set (X × ℝ)} (hU : IsOpen U)
    {value : X × ℝ → ℝ} {p : X} (hp : (p,0) ∈ U)
    (hv : Continuous (fun s : ℝ => value (p,s))) :
    componentInf U value p =
      ⨅ s ∈ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0, ENNReal.ofReal (value (p,s)) := by
  let C := connectedComponentIn {s : ℝ | (p,s) ∈ U} 0
  have hC : IsOpen C := (isOpen_section hU p).connectedComponentIn
  have hclosed : IsClosed {s : ℝ | componentInf U value p ≤ ENNReal.ofReal (value (p,s))} :=
    isClosed_le continuous_const (ENNReal.continuous_ofReal.comp hv)
  have hdense : C ⊆ closure (range ((↑) : ℚ → ℝ) ∩ C) :=
    by simpa [inter_comm] using Rat.denseRange_cast.open_subset_closure_inter hC
  have hle : ∀ s ∈ C, componentInf U value p ≤ ENNReal.ofReal (value (p,s)) := by
    intro s hs
    apply closure_minimal (t := {s : ℝ | componentInf U value p ≤ ENNReal.ofReal (value (p,s))})
      ?_ hclosed (hdense hs)
    rintro z ⟨⟨r,rfl⟩,hr⟩
    have hin := (segmentInside_iff_mem_component hp).mpr hr
    have h := iInf_le (fun r : ℚ => if SegmentInside U p (r : ℝ)
      then ENNReal.ofReal (value (p,(r : ℝ))) else ⊤) r
    simpa only [Set.mem_ofPred_eq, componentInf, ite_eq_left hin] using h
  apply le_antisymm
  · exact le_iInf fun s => le_iInf fun hs => hle s hs
  · unfold componentInf
    apply le_iInf
    intro r
    split_ifs with hr
    · exact iInf_le_of_le (r : ℝ) (iInf_le_of_le ((segmentInside_iff_mem_component hp).mp hr) le_rfl)
    · exact le_top

/-- Exceeding a nonnegative forward offset is precisely the compact-segment
condition. Openness is needed to replace membership of the endpoint by strict
inequality of the exit distance. -/
lemma lt_forwardExit_iff {U : Set (X × ℝ)} (hU : IsOpen U) {p : X} {r : ℝ}
    (hr : 0 ≤ r) : ENNReal.ofReal r < forwardExit U p ↔ SegmentInside U p r := by
  unfold forwardExit
  rw [lt_iSup_iff]
  constructor
  · rintro ⟨q,hq⟩
    split_ifs at hq with hin
    · have hrq := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mp hq
      intro s hs
      apply hin s
      rw [uIcc_of_le (hr.trans hrq.le), mem_Icc]
      rw [uIcc_of_le hr, mem_Icc] at hs
      exact ⟨hs.1, hs.2.trans hrq.le⟩
    · exact (not_lt_zero hq).elim
  · intro hin
    have hp := segmentInside_base hin
    have hrC := (segmentInside_iff_mem_component hp).mp hin
    have hopen := (isOpen_section hU p).connectedComponentIn (x := 0)
    obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hrC)
    obtain ⟨q,hrq,hqb⟩ := exists_rat_btwn hab.2
    have hqC := hsub ⟨hab.1.trans hrq,hqb⟩
    refine ⟨q, ?_⟩
    rw [ite_eq_left ((segmentInside_iff_mem_component hp).mpr hqC)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mpr hrq

omit [TopologicalSpace X] in
lemma segmentInside_reflect {U : Set (X × ℝ)} {p : X} {r : ℝ} :
    SegmentInside {z : X × ℝ | (z.1,-z.2) ∈ U} p r ↔ SegmentInside U p (-r) := by
  constructor <;> intro h s hs
  · have hm : -s ∈ uIcc 0 r := by
      simp only [mem_uIcc] at hs ⊢
      rcases hs with hs | hs
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    simpa using h (-s) hm
  · have hm : -s ∈ uIcc 0 (-r) := by
      simp only [mem_uIcc] at hs ⊢
      rcases hs with hs | hs
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    simpa using h (-s) hm

lemma lt_backwardExit_iff {U : Set (X × ℝ)} (hU : IsOpen U) {p : X} {r : ℝ}
    (hr : 0 ≤ r) : ENNReal.ofReal r < backwardExit U p ↔ SegmentInside U p (-r) := by
  have hV : IsOpen {z : X × ℝ | (z.1,-z.2) ∈ U} :=
    hU.preimage (continuous_fst.prodMk continuous_snd.neg)
  have heq : backwardExit U p = forwardExit {z : X × ℝ | (z.1,-z.2) ∈ U} p := by
    simp only [backwardExit, forwardExit, segmentInside_reflect]
  rw [heq, lt_forwardExit_iff hV hr, segmentInside_reflect]

lemma forwardExit_pos {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) : 0 < forwardExit U p := by
  simpa using (lt_forwardExit_iff hU (p := p) (r := 0) le_rfl).mpr
    (segmentInside_zero.mpr hp)

lemma backwardExit_pos {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) : 0 < backwardExit U p := by
  simpa using (lt_backwardExit_iff hU (p := p) (r := 0) le_rfl).mpr
    (by simpa using (segmentInside_zero (p := p)).mpr hp)

lemma component_eq_Ioo {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) (hf : forwardExit U p ≠ ⊤) (hb : backwardExit U p ≠ ⊤) :
    connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 =
      Ioo (-(backwardExit U p).toReal) (forwardExit U p).toReal := by
  have hfp : 0 < (forwardExit U p).toReal := ENNReal.toReal_pos (forwardExit_pos hU hp).ne' hf
  have hbp : 0 < (backwardExit U p).toReal := ENNReal.toReal_pos (backwardExit_pos hU hp).ne' hb
  ext r
  rw [← segmentInside_iff_mem_component hp, mem_Ioo]
  by_cases hr : 0 ≤ r
  · rw [← lt_forwardExit_iff hU hr, ENNReal.ofReal_lt_iff_lt_toReal hr hf]
    exact ⟨fun h => ⟨by linarith,h⟩, fun h => h.2⟩
  · have hnr : 0 ≤ -r := by linarith
    have he := lt_backwardExit_iff hU (p := p) hnr
    rw [neg_neg] at he
    rw [← he, ENNReal.ofReal_lt_iff_lt_toReal hnr hb]
    constructor
    · intro h; constructor <;> linarith
    · intro h; linarith [h.1]

lemma volume_component {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) (hfin : componentLength U p ≠ ⊤) :
    volume (connectedComponentIn {s : ℝ | (p,s) ∈ U} 0) = componentLength U p := by
  have hf : forwardExit U p ≠ ⊤ := by
    exact (ENNReal.add_ne_top.mp hfin).1
  have hb : backwardExit U p ≠ ⊤ := by
    exact (ENNReal.add_ne_top.mp hfin).2
  rw [component_eq_Ioo hU hp hf hb, Real.volume_Ioo, sub_neg_eq_add]
  rw [ENNReal.ofReal_add (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg),
    ENNReal.ofReal_toReal hf, ENNReal.ofReal_toReal hb]
  rfl

section Measurability
variable [MeasurableSpace X] [BorelSpace X]

lemma measurable_forwardExit {U : Set (X × ℝ)} (hU : IsOpen U) : Measurable (forwardExit U) := by
  apply Measurable.iSup
  intro r
  exact Measurable.ite (isOpen_segmentInside hU (r : ℝ)).measurableSet
    measurable_const measurable_const

lemma measurable_backwardExit {U : Set (X × ℝ)} (hU : IsOpen U) : Measurable (backwardExit U) := by
  apply Measurable.iSup
  intro r
  exact Measurable.ite (isOpen_segmentInside hU (-(r : ℝ))).measurableSet
    measurable_const measurable_const

lemma measurable_componentLength {U : Set (X × ℝ)} (hU : IsOpen U) :
    Measurable (componentLength U) :=
  (measurable_forwardExit hU).add (measurable_backwardExit hU)

lemma measurable_componentInf {U : Set (X × ℝ)} (hU : IsOpen U)
    {value : X × ℝ → ℝ} (hvalue : Measurable value) : Measurable (componentInf U value) := by
  apply Measurable.iInf
  intro r
  exact Measurable.ite (isOpen_segmentInside hU (r : ℝ)).measurableSet
    ((hvalue.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal) measurable_const

lemma measurable_componentWeight {U : Set (X × ℝ)} (hU : IsOpen U)
    {h d : X × ℝ → ℝ} (hh : Measurable h) (hd : Measurable d) (δ : ℝ) :
    Measurable (componentWeight U h d δ) := by
  apply Measurable.ite _ (measurable_componentInf hU hh) measurable_const
  apply MeasurableSet.inter
  · exact (hU.preimage (continuous_id.prodMk continuous_const)).measurableSet
  · apply MeasurableSet.inter
    · exact (measurable_componentLength hU (measurableSet_singleton ⊤)).compl
    · exact measurableSet_le (measurable_componentLength hU)
        (measurable_const.mul (measurable_componentInf hU hd))

end Measurability
end HenonLaneEmden.LineComponents
end Components

end OAI
