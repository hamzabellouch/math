import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservedUnordered
import OAI.Analysis.CoulombRadii.Packets.OriginalPotentialTower
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalRetainedLikelihood

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
namespace NeutralAtom

lemma measurable_conditionalPacketDensity_data {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (y : Position) :
    Measurable (fun datum => conditionalPacketDensity P raw obs g c r₀ s datum y) := by
  exact (((continuous_rawPacketDensity hg hc hr hs).comp
    (continuous_id.prodMk continuous_const)).stronglyMeasurable.integral_kernel
      (κ:=ProbabilityTheory.condDistrib raw obs P)).measurable

lemma measurable_conditionalPacketPotential_data {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (y : Position) :
    Measurable (fun datum => potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) y) := by
  have H := ((measurable_rawPacketPotential (n:=n) hg hc hr hs y).stronglyMeasurable.integral_kernel
      (κ:=ProbabilityTheory.condDistrib raw obs P)).measurable
  convert H using 1
  funext datum
  exact mixturePacketPotential hg hgs hm hc hr hs _ y

lemma measurable_packetKernel_center {g : Position → ℝ} (hg : Continuous g)
    {c r₀ s : ℝ} (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (y : Position) :
    Measurable (fun x => packetKernel g c r₀ s x y) := by
  exact ((continuous_packetKernel hg hc hr hs).comp
    (continuous_id.prodMk continuous_const)).measurable
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace NeutralAtom

lemma measureReal_mono_ae_of_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {A B : Set Ω} (h : A ≤ᵐ[P] B) : P.real A ≤ P.real B :=
  ENNReal.toReal_mono (measure_ne_top P B) (measure_mono_ae h)

lemma posterior_inverse_failure_transfer {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] (P : Measure Ω) [IsFiniteMeasure P]
    {obs : Ω → B} (hobs : Measurable obs) {μ H S C : B → ℝ}
    (hH : Measurable H) (hS : Measurable S) (hC : Measurable C)
    {m q e L U p : ℝ}
    (hmatch : ∀ᵐ z ∂P, C (obs z) ≤ m → |μ (obs z)-S (obs z)| ≤ e)
    (hhi : ∀ {A : Set B}, MeasurableSet A →
      (∀ d∈A, C d ≤ m) → (∀ d∈A, q-e ≤ S d) → (∀ d∈A,H d ≤ L) → P.real (obs ⁻¹' A) ≤ p)
    (hlo : ∀ {A : Set B}, MeasurableSet A →
      (∀ d∈A, C d ≤ m) → (∀ d∈A, S d ≤ q+e) → (∀ d∈A,U ≤ H d) → P.real (obs ⁻¹' A) ≤ p) :
    P.real {z | C (obs z) ≤ m ∧ q ≤ μ (obs z) ∧ H (obs z) ≤ L} ≤ p ∧
    P.real {z | C (obs z) ≤ m ∧ μ (obs z) ≤ q ∧ U ≤ H (obs z)} ≤ p := by
  have transfer {event : Set Ω} {dataEvent : Set B} (hmeas : MeasurableSet dataEvent)
      (hsub : event ≤ᵐ[P] obs ⁻¹' dataEvent) : P.real event ≤ P.real (obs ⁻¹' dataEvent) := by
    have hnull : P.real (event \ obs ⁻¹' dataEvent) = 0 := by
      simp only [measureReal_def, ae_le_set.mp hsub, ENNReal.toReal_zero]
    rw [← measureReal_inter_add_sdiff (hmeas.preimage hobs), hnull, add_zero]
    exact measureReal_mono Set.inter_subset_right
  have hmeasHi : MeasurableSet {datum | C datum ≤ m ∧ q-e ≤ S datum ∧ H datum ≤ L} :=
    (measurableSet_le hC measurable_const).inter
      ((measurableSet_le measurable_const hS).inter (measurableSet_le hH measurable_const))
  have hmeasLo : MeasurableSet {datum | C datum ≤ m ∧ S datum ≤ q+e ∧ U ≤ H datum} :=
    (measurableSet_le hC measurable_const).inter
      ((measurableSet_le hS measurable_const).inter (measurableSet_le measurable_const hH))
  have Hhi := hhi (A:={d | C d ≤ m ∧ q-e ≤ S d ∧ H d ≤ L}) hmeasHi
    (fun _ hd =>hd.1) (fun _ hd =>hd.2.1) (fun _ hd =>hd.2.2)
  have Hlo := hlo (A:={d | C d ≤ m ∧ S d ≤ q+e ∧ U ≤ H d}) hmeasLo
    (fun _ hd =>hd.1) (fun _ hd =>hd.2.1) (fun _ hd =>hd.2.2)
  constructor
  · exact (transfer hmeasHi (by
      filter_upwards [hmatch] with z hz
      intro hd
      exact ⟨hd.1,by linarith [(abs_le.mp (hz hd.1)).2,hd.2.1],hd.2.2⟩)).trans Hhi
  · exact (transfer hmeasLo (by
      filter_upwards [hmatch] with z hz
      intro hd
      exact ⟨hd.1,by linarith [(abs_le.mp (hz hd.1)).1,hd.2.1],hd.2.2⟩)).trans Hlo

@[simp] lemma unorderedSum_retainedTailObservation {n J : ℕ} {j : ℕ}
    (k : RetainedScales J j) (f : Position → ℝ)
    (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) :
    unorderedSum f (retainedTailObservation j z k.val)=
      ∑ i,f (observationArrayPositions k z i) := by
  simp only [retainedTailObservation,dite_eq_left k.property,unorderedSum_forgetOrder]

@[simp] lemma unorderedSum_tailObservation {n J : ℕ} (r : Fin J → ℝ) {j : ℕ}
    (k : Fin J) (hk : j ≤ k.val) (f : Position → ℝ) (z : ObservationSample n J) :
    unorderedSum f (tailObservation r j z k)=∑ i,f (observedOrdered r k z i) := by
  simp only [tailObservation,ite_eq_left hk,observedArray,unorderedSum_forgetOrder]

lemma retained_inverse_gate_transfer {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] (r : Fin J → ℝ) {j : ℕ} (k : RetainedScales J j)
    {ball : Set Position} (hb : MeasurableSet ball) {f : Position → ℝ} (hf : Measurable f)
    {μ H : (Fin J → UnorderedArray n) → ℝ} (hH : Measurable H) {m e q L U p : ℝ}
    (hmatch : ∀ᵐ z ∂observationLaw J ν, rawCount ball (observedOrdered r k.val z) ≤ m →
      |μ (tailObservation r j z)-(∑ i,f (observedOrdered r k.val z i))| ≤ e)
    (hhi : ∀ {B : Set (Fin J → UnorderedArray n)}, MeasurableSet B →
      (∀ z∈retainedTailObservation j ⁻¹' B,rawCount ball (observationArrayPositions k z) ≤ m) →
      (∀ z∈retainedTailObservation j ⁻¹' B,q-e ≤ ∑ i,f (observationArrayPositions k z i)) →
      (∀ᵐ z ∂observationLaw J ν,z∈tailObservation r j ⁻¹' B → H (tailObservation r j z) ≤ L) →
      (observationLaw J ν).real (tailObservation r j ⁻¹' B) ≤ p)
    (hlo : ∀ {B : Set (Fin J → UnorderedArray n)}, MeasurableSet B →
      (∀ z∈retainedTailObservation j ⁻¹' B,rawCount ball (observationArrayPositions k z) ≤ m) →
      (∀ z∈retainedTailObservation j ⁻¹' B,(∑ i,f (observationArrayPositions k z i)) ≤ q+e) →
      (∀ᵐ z ∂observationLaw J ν,z∈tailObservation r j ⁻¹' B → U ≤ H (tailObservation r j z)) →
      (observationLaw J ν).real (tailObservation r j ⁻¹' B) ≤ p) :
    (observationLaw J ν).real {z | rawCount ball (observedOrdered r k.val z) ≤ m ∧
      q ≤ μ (tailObservation r j z) ∧ H (tailObservation r j z) ≤ L} ≤ p ∧
    (observationLaw J ν).real {z | rawCount ball (observedOrdered r k.val z) ≤ m ∧
      μ (tailObservation r j z) ≤ q ∧ U ≤ H (tailObservation r j z)} ≤ p := by
  let C := fun datum : Fin J → UnorderedArray n =>
    unorderedSum (ball.indicator (fun _ => (1:ℝ))) (datum k.val)
  let S := fun datum : Fin J → UnorderedArray n => unorderedSum f (datum k.val)
  have hS : Measurable S := (measurable_unorderedSum hf).comp (measurable_pi_apply k.val)
  have hC : Measurable C := (measurable_unorderedSum
    (measurable_const.indicator hb)).comp (measurable_pi_apply k.val)
  have hcount (z : ObservationSample n J) :
      C (tailObservation r j z)=rawCount ball (observedOrdered r k.val z) := by
    simp only [C,unorderedSum_tailObservation r k.val k.property,rawCount]
  have hsum (z : ObservationSample n J) :
      S (tailObservation r j z)=∑ i,f (observedOrdered r k.val z i) := by
    simp only [S,unorderedSum_tailObservation r k.val k.property]
  have hcRet (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) :
      C (retainedTailObservation j z)=rawCount ball (observationArrayPositions k z) := by
    simp only [C,unorderedSum_retainedTailObservation,rawCount]
  have hsRet (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) :
      S (retainedTailObservation j z)=∑ i,f (observationArrayPositions k z i) := by
    simp only [S,unorderedSum_retainedTailObservation]
  have HH := posterior_inverse_failure_transfer (observationLaw J ν)
    (measurable_tailObservation r j) hH hS hC (by simpa only [hcount,hsum] using hmatch)
    (q:=q) (L:=L) (U:=U) (p:=p)
    (by
      intro B hB hcnt hgate hfld
      apply hhi hB
      · intro z hz; rw [←hcRet]; exact hcnt _ hz
      · intro z hz; rw [←hsRet]; exact hgate _ hz
      · exact Eventually.of_forall (fun z hz => hfld _ hz))
    (by
      intro B hB hcnt hgate hfld
      apply hlo hB
      · intro z hz; rw [←hcRet]; exact hcnt _ hz
      · intro z hz; rw [←hsRet]; exact hgate _ hz
      · exact Eventually.of_forall (fun z hz => hfld _ hz))
  simpa only [hcount] using HH
end NeutralAtom

end

end OAI
