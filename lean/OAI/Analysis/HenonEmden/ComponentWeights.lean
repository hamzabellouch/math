import OAI.Analysis.HenonEmden.Components

namespace OAI

universe uX uP

section ComponentWeights
open MeasureTheory Set Filter Topology
open scoped ENNReal
open Classical
namespace HenonLaneEmden.LineComponents
variable {X : Type uX} [TopologicalSpace X]

omit [TopologicalSpace X] in
lemma forwardExit_le_volume_component {U : Set (X × ℝ)} {p : X}
    (_hp : (p,0) ∈ U) :
    forwardExit U p ≤ volume (connectedComponentIn {s : ℝ | (p,s) ∈ U} 0) := by
  unfold forwardExit
  apply iSup_le
  intro r
  split_ifs with hr
  · by_cases hpos : 0 ≤ (r : ℝ)
    · have hs : uIcc 0 (r : ℝ) ⊆ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 :=
        isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hr
      have hv := measure_mono (μ := (volume : Measure ℝ)) hs
      simpa only [uIcc_of_le hpos,Real.volume_Icc,sub_zero] using hv
    · simp only [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hpos),zero_le]
  · exact bot_le

omit [TopologicalSpace X] in
lemma backwardExit_le_volume_component {U : Set (X × ℝ)} {p : X}
    (_hp : (p,0) ∈ U) :
    backwardExit U p ≤ volume (connectedComponentIn {s : ℝ | (p,s) ∈ U} 0) := by
  unfold backwardExit
  apply iSup_le
  intro r
  split_ifs with hr
  · by_cases hpos : 0 ≤ (r : ℝ)
    · have hs : uIcc 0 (-(r : ℝ)) ⊆ connectedComponentIn {s : ℝ | (p,s) ∈ U} 0 :=
        isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hr
      have hv := measure_mono (μ := (volume : Measure ℝ)) hs
      simpa only [uIcc_of_ge (neg_nonpos.mpr hpos),Real.volume_Icc,zero_sub,neg_neg] using hv
    · simp only [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hpos),zero_le]
  · exact bot_le

/-- The rational exit construction gives the genuine Lebesgue length, including
unbounded components, not merely the finite case. -/
lemma volume_component_all {U : Set (X × ℝ)} (hU : IsOpen U) {p : X}
    (hp : (p,0) ∈ U) :
    volume (connectedComponentIn {s : ℝ | (p,s) ∈ U} 0) = componentLength U p := by
  by_cases hfin : componentLength U p ≠ ⊤
  · exact volume_component hU hp hfin
  · have ht : componentLength U p = ⊤ := not_ne_iff.mp hfin
    rw [ht]
    by_contra hv
    apply hfin
    exact ENNReal.add_ne_top.mpr
      ⟨ne_top_of_le_ne_top hv (forwardExit_le_volume_component hp),
       ne_top_of_le_ne_top hv (backwardExit_le_volume_component hp)⟩

/-- The family that observes a single real layer relative to a moving basepoint. -/
def shiftedLayer (U : Set ℝ) : Set (ℝ × ℝ) := {z | z.1+z.2 ∈ U}

lemma isOpen_shiftedLayer {U : Set ℝ} (hU : IsOpen U) : IsOpen (shiftedLayer U) :=
  hU.preimage (continuous_fst.add continuous_snd)

lemma image_relative_component {U : Set ℝ} {x : ℝ} (hx : x ∈ U) :
    (fun r : ℝ => x+r) '' connectedComponentIn {r : ℝ | (x,r) ∈ shiftedLayer U} 0 =
      connectedComponentIn U x := by
  let H := Homeomorph.addLeft x
  have hs : H '' {r : ℝ | (x,r) ∈ shiftedLayer U} = U := by
    change H '' H ⁻¹' U = U
    exact image_preimage_eq U H.surjective
  have hzero : 0 ∈ {r : ℝ | (x,r) ∈ shiftedLayer U} := by simpa [shiftedLayer] using hx
  have hh := H.image_connectedComponentIn hzero
  rw [hs] at hh
  change (fun r : ℝ => x+r) '' connectedComponentIn {r : ℝ | (x,r) ∈ shiftedLayer U} 0 =
    connectedComponentIn U (x+0) at hh
  simpa only [add_zero] using hh

lemma shifted_componentInf_eq {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    {f : ℝ → ℝ} (hf : Continuous f) :
    componentInf (shiftedLayer U) (fun z => f (z.1+z.2)) x =
      ⨅ y ∈ connectedComponentIn U x, ENNReal.ofReal (f y) := by
  rw [componentInf_eq_component (isOpen_shiftedLayer hU) (by simpa [shiftedLayer] using hx)
    (hf.comp (continuous_const.add continuous_id)), ← image_relative_component hx, iInf_image]

lemma shifted_componentLength_eq {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    componentLength (shiftedLayer U) x = volume (connectedComponentIn U x) := by
  rw [← volume_component_all (isOpen_shiftedLayer hU) (by simpa [shiftedLayer] using hx),
      ← image_relative_component hx]
  have hm := measure_preimage_add volume x
    ((fun r : ℝ => x+r) '' connectedComponentIn {r : ℝ | (x,r) ∈ shiftedLayer U} 0)
  rw [preimage_image_eq _ (by intro a b hab; linarith : Function.Injective (fun r : ℝ => x+r))] at hm
  exact hm


/-- A connected real set of finite length is bounded; this rules out every
unbounded line-component case without choosing fictitious infinite endpoints. -/
lemma bounded_of_connected_volume_ne_top {I : Set ℝ} (hc : IsConnected I)
    (hv : volume I ≠ ⊤) : BddBelow I ∧ BddAbove I := by
  obtain ⟨x,hx⟩ := hc.nonempty
  constructor
  · by_contra h
    have hs : Iio x ⊆ I := by
      intro z hz
      obtain ⟨y,hy,hyz⟩ := not_bddBelow_iff.mp h z
      exact hc.Icc_subset hy hx ⟨hyz.le,hz.le⟩
    have hm := measure_mono (μ := (volume : Measure ℝ)) hs
    rw [Real.volume_Iio] at hm
    exact hv (top_le_iff.mp hm)
  · by_contra h
    have hs : Ioi x ⊆ I := by
      intro z hz
      obtain ⟨y,hy,hzy⟩ := not_bddAbove_iff.mp h z
      exact hc.Icc_subset hx hy ⟨hz.le,hzy.le⟩
    have hm := measure_mono (μ := (volume : Measure ℝ)) hs
    rw [Real.volume_Ioi] at hm
    exact hv (top_le_iff.mp hm)

noncomputable def setInf (f : ℝ → ℝ) (I : Set ℝ) : ℝ≥0∞ :=
  ⨅ y ∈ I, ENNReal.ofReal (f y)

/-- The component weight, including the zero continuation when
the set is empty or the length condition fails. -/
noncomputable def setWeight (h d : ℝ → ℝ) (δ : ℝ) (I : Set ℝ) : ℝ≥0∞ :=
  if I.Nonempty ∧ volume I ≠ ⊤ ∧ volume I ≤ ENNReal.ofReal (2*δ)*setInf d I
  then setInf h I else 0

lemma setInf_le {f : ℝ → ℝ} {I : Set ℝ} {x : ℝ} (hx : x ∈ I) :
    setInf f I ≤ ENNReal.ofReal (f x) :=
  iInf_le_of_le x (iInf_le_of_le hx le_rfl)

lemma setWeight_le {h d : ℝ → ℝ} {δ : ℝ} {I : Set ℝ} {x : ℝ} (hx : x ∈ I) :
    setWeight h d δ I ≤ ENNReal.ofReal (h x) := by
  unfold setWeight
  split_ifs
  · exact setInf_le hx
  · exact bot_le

lemma setWeight_ne_top {h d : ℝ → ℝ} {δ : ℝ} {I : Set ℝ} :
    setWeight h d δ I ≠ ⊤ := by
  unfold setWeight
  split_ifs with hI
  · obtain ⟨x,hx⟩ := hI.1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (setInf_le hx)
  · exact ENNReal.zero_ne_top

lemma setWeight_eq_zero_of_empty (h d : ℝ → ℝ) (δ : ℝ) :
    setWeight h d δ ∅ = 0 := by simp [setWeight]

lemma setWeight_pos_bounded {h d : ℝ → ℝ} {δ : ℝ} {I : Set ℝ}
    (hc : IsConnected I) (hp : 0 < (setWeight h d δ I).toReal) :
    BddBelow I ∧ BddAbove I := by
  apply bounded_of_connected_volume_ne_top hc
  unfold setWeight at hp
  split_ifs at hp with hI
  · exact hI.2.1
  · simp only [ENNReal.toReal_zero,lt_self_iff_false] at hp

lemma componentWeight_eq_setWeight {U : Set (X × ℝ)} (hU : IsOpen U)
    {h d : X × ℝ → ℝ} {p : X} (hh : Continuous (fun s => h (p,s)))
    (hd : Continuous (fun s => d (p,s))) (δ : ℝ) :
    componentWeight U h d δ p = setWeight (fun s => h (p,s)) (fun s => d (p,s)) δ
      (connectedComponentIn {s | (p,s) ∈ U} 0) := by
  by_cases hp : (p,0) ∈ U
  · have hne : (connectedComponentIn {s | (p,s) ∈ U} 0).Nonempty :=
      ⟨0,mem_connectedComponentIn hp⟩
    simp only [componentWeight,setWeight,hp,hne,true_and,volume_component_all hU hp,
      componentInf_eq_component hU hp hh,componentInf_eq_component hU hp hd,setInf]
  · simp only [componentWeight,hp,false_and,ite_false,
      connectedComponentIn_eq_empty (show 0 ∉ {s | (p,s) ∈ U} from hp),
      setWeight_eq_zero_of_empty]

lemma shifted_componentWeight_eq {U : Set ℝ} (hU : IsOpen U)
    {h d : ℝ → ℝ} (hh : Continuous h) (hd : Continuous d) (δ x : ℝ) :
    componentWeight (shiftedLayer U) (fun z => h (z.1+z.2))
      (fun z => d (z.1+z.2)) δ x = setWeight h d δ (connectedComponentIn U x) := by
  by_cases hx : x ∈ U
  · have hne : (connectedComponentIn U x).Nonempty := ⟨x,mem_connectedComponentIn hx⟩
    have hpx : (x,0) ∈ shiftedLayer U := by simpa [shiftedLayer] using hx
    simp only [componentWeight,setWeight,hpx,hne,true_and,
      shifted_componentLength_eq hU hx,shifted_componentInf_eq hU hx hh,
      shifted_componentInf_eq hU hx hd,setInf]
  · simp [componentWeight,shiftedLayer,hx,connectedComponentIn_eq_empty hx,setWeight]

lemma measurable_setWeight_component {U : Set ℝ} (hU : IsOpen U)
    {h d : ℝ → ℝ} (hh : Continuous h) (hd : Continuous d) (δ : ℝ) :
    Measurable (fun x => setWeight h d δ (connectedComponentIn U x)) := by
  have he : (fun x => setWeight h d δ (connectedComponentIn U x)) =
      componentWeight (shiftedLayer U) (fun z => h (z.1+z.2)) (fun z => d (z.1+z.2)) δ := by
    funext x
    exact (shifted_componentWeight_eq hU hh hd δ x).symm
  rw [he]
  exact measurable_componentWeight (isOpen_shiftedLayer hU)
    (hh.measurable.comp (measurable_fst.add measurable_snd))
    (hd.measurable.comp (measurable_fst.add measurable_snd)) δ

section Parameter
variable {P : Type uP} [TopologicalSpace P]

def relativeLayer (U : Set (P × ℝ)) : Set ((P × ℝ) × ℝ) :=
  {z | (z.1.1,z.1.2+z.2) ∈ U}

lemma isOpen_relativeLayer {U : Set (P × ℝ)} (hU : IsOpen U) : IsOpen (relativeLayer U) :=
  hU.preimage ((continuous_fst.fst).prodMk (continuous_fst.snd.add continuous_snd))

lemma relative_componentWeight_eq {U : Set (P × ℝ)} (hU : IsOpen U)
    {h d : P × ℝ → ℝ} (hh : Continuous h) (hd : Continuous d) (δ : ℝ) (p : P × ℝ) :
    componentWeight (relativeLayer U) (fun z => h (z.1.1,z.1.2+z.2))
      (fun z => d (z.1.1,z.1.2+z.2)) δ p =
    setWeight (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ
      (connectedComponentIn {s | (p.1,s) ∈ U} p.2) := by
  have he := shifted_componentWeight_eq (isOpen_section hU p.1)
    (h := fun s => h (p.1,s)) (d := fun s => d (p.1,s))
    (hh.comp (continuous_const.prodMk continuous_id))
    (hd.comp (continuous_const.prodMk continuous_id)) δ p.2
  simpa only [componentWeight,componentLength,forwardExit,backwardExit,componentInf,
    SegmentInside,relativeLayer,shiftedLayer,Set.mem_ofPred] using he


variable [MeasurableSpace P] [BorelSpace P]
lemma measurable_parametric_setWeight {U : Set (P × ℝ)} (hU : IsOpen U)
    {h d : P × ℝ → ℝ} (hh : Continuous h) (hd : Continuous d) (δ : ℝ) :
    Measurable (fun p : P × ℝ =>
      setWeight (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ
        (connectedComponentIn {s | (p.1,s) ∈ U} p.2)) := by
  have he : (fun p : P × ℝ =>
      setWeight (fun s => h (p.1,s)) (fun s => d (p.1,s)) δ
        (connectedComponentIn {s | (p.1,s) ∈ U} p.2)) =
      componentWeight (relativeLayer U) (fun z => h (z.1.1,z.1.2+z.2))
        (fun z => d (z.1.1,z.1.2+z.2)) δ := by
    funext p
    exact (relative_componentWeight_eq hU hh hd δ p).symm
  rw [he]
  exact measurable_componentWeight (isOpen_relativeLayer hU)
    (hh.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd)))
    (hd.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd))) δ

end Parameter

end HenonLaneEmden.LineComponents
end ComponentWeights

end OAI
