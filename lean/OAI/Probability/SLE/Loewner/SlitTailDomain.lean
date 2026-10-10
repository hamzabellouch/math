import OAI.Probability.SLE.Loewner.SlitRadialLimits
import OAI.Probability.SLE.Loewner.RawRadialTipBoundary
import OAI.Probability.SLE.Loewner.SmoothRawDomain

namespace OAI

/-! The raw survival domain of a finite slit with constant driving tail
is exactly its geometric slit domain. -/
noncomputable section
open Set Filter Function Complex _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

lemma slitCapacity_raw_initial_range (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {t : ℝ≥0}
    (ht : t ≤ slitCapacityHorizon p hi h0 hH T) :
    (fun s : ℝ≥0 => Target.trace 1 (slitCapacityDriver p hi h0 hH hT) s) '' Icc 0 t=
      slitCapacityCurve p hi h0 hH T '' Icc 0 t := by
  apply image_congr
  intro s hs
  exact slitCapacity_raw_trace_eq p hi h0 hH hT (hs.2.trans ht)

theorem slitCapacity_raw_complement_survives (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) (t : ℝ≥0) {z : ℂ}
    (hz : z∈upperHalfPlane \ ((fun s : ℝ≥0 =>
      Target.trace 1 (slitCapacityDriver p hi h0 hH hT) s) '' Icc 0 t)) :
    Target.Surviving 1 (slitCapacityDriver p hi h0 hH hT) z t := by
  let b := slitCapacityDriver p hi h0 hH hT
  let A := slitCapacityHorizon p hi h0 hH T
  let u := initialDrivingValue p hi h0 hH T hT
  let β := fun s : ℝ≥0 => Target.trace 1 b s
  change z∈upperHalfPlane \ (β '' Icc 0 t) at hz
  by_cases ht : t ≤ A
  · change z∈{z | Target.Surviving 1 b z t}
    rw [slitCapacity_surviving_eq p hi h0 hH hT ht,
      ←slitCapacityCurve_initial_range p hi h0 hH T ht,
      ←slitCapacity_raw_initial_range p hi h0 hH hT ht]
    exact hz
  have hAt : A<t := lt_of_not_ge ht
  have hpre : z∈upperHalfPlane \ (β '' Icc 0 A) :=
    ⟨hz.1,fun he => hz.2 (image_mono (Icc_subset_Icc_right hAt.le) he)⟩
  have hsA : Target.Surviving 1 b z A := by
    change z∈{z | Target.Surviving 1 b z A}
    rw [slitCapacity_surviving_eq p hi h0 hH hT le_rfl,
      ←slitCapacityCurve_initial_range p hi h0 hH T le_rfl,
      ←slitCapacity_raw_initial_range p hi h0 hH hT le_rfl]
    exact hpre
  let w := Target.flow 1 b z A-(u:ℂ)
  have hw : w∈upperHalfPlane := by
    have hh := Target.surviving_flow_mem_upperHalfPlane 1 b z A A.coe_nonneg hsA
    simpa only [w,upperHalfPlane,mem_ofPred_eq,sub_im,ofReal_im,sub_zero] using hh
  have hshift : (u:ℂ)+w=Target.flow 1 b z A := by dsimp [w]; ring
  have hb : ∀ s : ℝ≥0, A ≤ s → b s=u :=
    fun s hs => slitCapacityDriver_after p hi h0 hH hT hs
  have hs : Target.Surviving 1 (Target.linearDriver 0) w (t-A : ℝ≥0) := by
    by_contra hn
    obtain ⟨v,hv,hvS,he⟩ := Target.exists_trace_time_of_not_surviving (Target.linearDriver 0)
      w hw (t-A) hn (fun _ => 0) 0
      (fun s hs => Target.linearDriver_derivative 0 s hs) (fun _ _ => by simp)
    have hval : β (A+v)=z := by
      dsimp only [β]
      rw [NNReal.coe_add,Target.trace_constant_tail b A v hv u hb,←he,hshift]
      exact Target.inverseFlow_eq_of_surviving 1 b A A.coe_nonneg z _ hsA rfl
    apply hz.2
    refine ⟨A+v,⟨zero_le,?_⟩,hval⟩
    calc A+v ≤ A+(t-A) := add_le_add le_rfl hvS
         _ = t := add_tsub_cancel_of_le hAt.le
  let q := (u:ℂ)+Target.flow 1 (Target.linearDriver 0) w (t-A : ℝ≥0)
  have hq : q∈upperHalfPlane := by
    have hh := Target.surviving_flow_mem_upperHalfPlane 1 (Target.linearDriver 0) w
      (t-A : ℝ≥0) (t-A).coe_nonneg hs
    simpa only [q,upperHalfPlane,mem_ofPred_eq,add_im,ofReal_im,zero_add] using hh
  have hF : Target.inverseFlow 1 b t q=z := by
    have he := Target.inverseFlow_constant_tail b A (t-A) u hb hq
    rw [←NNReal.coe_add,add_tsub_cancel_of_le hAt.le] at he
    rw [he]
    have hqsub : q-(u:ℂ)=Target.flow 1 (Target.linearDriver 0) w (t-A : ℝ≥0) := by
      dsimp [q]; ring
    rw [hqsub,Target.inverseFlow_eq_of_surviving 1 (Target.linearDriver 0)
      (t-A : ℝ≥0) (t-A).coe_nonneg w _ hs rfl,hshift]
    exact Target.inverseFlow_eq_of_surviving 1 b A A.coe_nonneg z _ hsA rfl
  rw [←hF]
  exact Target.inverseFlow_surviving 1 (by norm_num) b t q hq

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}

theorem RegularSLEPresentation.slitCapacity_raw_domains
    (a : RegularSLEPresentation P κ γ) (hκ : 0<κ)
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT0 : 0<T) (hT : T<1) (t : ℝ≥0) :
    {z | Target.Surviving 1 (slitCapacityDriver p hi h0 hH hT) z t}=
      survivingDomain (fun s : ℝ≥0 => Target.trace 1 (slitCapacityDriver p hi h0 hH hT) s) t := by
  let b := slitCapacityDriver p hi h0 hH hT
  let β := fun s : ℝ≥0 => Target.trace 1 b s
  obtain ⟨_,_,_,_,hfree⟩ := a.slitCapacity_raw_geometry hκ p hi h0 hH hT0 hT
  have hsub (t : ℝ≥0) (ht : 0<t) : {z | Target.Surviving 1 b z t} ⊆ survivingDomain β t := by
    intro z hz
    apply hfree t ht
    refine ⟨Target.surviving_mem_upperHalfPlane 1 b z t t.coe_nonneg hz,?_⟩
    rintro ⟨s,hs,he⟩
    have hp := Target.surviving_of_le_time 1 b z s.coe_nonneg hs.2 hz
    change Target.trace 1 b s=z at he
    rw [←he] at hp
    exact a.raw_radial_tip_not_surviving hκ b s _
      (slitCapacity_radial_limit p hi h0 hH hT s) hp
  apply Subset.antisymm
  · intro z hz
    obtain ⟨S,hSt,hSz⟩ := Target.exists_later_survival 1 b z t.coe_nonneg hz
    let S' : ℝ≥0 := ⟨S,t.coe_nonneg.trans hSt.le⟩
    exact survivingDomain_antitone β (show t ≤ S' from hSt.le)
      (hsub S' (t.coe_nonneg.trans_lt hSt) hSz)
  · intro z hz
    exact slitCapacity_raw_complement_survives p hi h0 hH hT t hz.1

end SLEExactGauge

end

end OAI
