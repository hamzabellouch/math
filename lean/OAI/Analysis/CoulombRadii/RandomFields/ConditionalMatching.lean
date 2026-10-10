import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalDensity
import OAI.Analysis.CoulombRadii.FormDomain.ExplicitMultiplyGradient
import OAI.Analysis.CoulombRadii.Packets.PatchKernelDuality

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace NeutralAtom

theorem condExp_matching {α : Type*} [m₀ : MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {m : MeasurableSpace α}
    (hm : m ≤ m₀) {f g e : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (he : Integrable e μ)
    (hgm : StronglyMeasurable[m] g) (hem : StronglyMeasurable[m] e)
    (hfg : ∀ᵐ z ∂μ, |f z-g z|≤e z) :
    ∀ᵐ z ∂μ, |(μ[f|m]) z-g z|≤e z := by
  have hupper := condExp_mono hf (hg.add he) (hfg.mono (fun z hz => by
    have hh := (abs_le.mp hz).2
    change f z≤g z+e z
    linarith)) (m := m)
  have hlower := condExp_mono (hg.sub he) hf (hfg.mono (fun z hz => by
    have hh := (abs_le.mp hz).1
    change g z-e z≤f z
    linarith)) (m := m)
  rw [condExp_of_stronglyMeasurable hm (hgm.add hem) (hg.add he)] at hupper
  rw [condExp_of_stronglyMeasurable hm (hgm.sub hem) (hg.sub he)] at hlower
  filter_upwards [hupper,hlower] with z hu hl
  change _≤g z+e z at hu
  change g z-e z≤_ at hl
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end NeutralAtom

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

theorem master_kernel_posterior_matching (g : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hgn : (∫ z, g z^2)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
      (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
      (raw : Ω → Configuration n) (obs : Ω → B) (array : B → Configuration n),
    MeasurePreserving raw P ν → Measurable obs → Measurable array →
    ∀ (y : Position) {d : ℝ}, 0≤d →
    (∀ᵐ z ∂P, ∃ p : Equiv.Perm (Fin n), ∀ i, ‖raw z (p i)-array (obs z) i‖≤d) →
    ∀ᵐ z ∂P,
      |conditionalPacketDensity P raw obs g c r₀ s (obs z) y-
        rawPacketDensity g c r₀ s (array (obs z)) y|≤
      (C/(packetWidth c r₀ s y)^4*d)*
        rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+d)) (array (obs z)) := by
  obtain ⟨C,hC,H⟩ := master_kernel_estimates g hg hgn
  refine ⟨C,hC,?_⟩
  intro c r₀ s hc hr hs hq Ω B mΩ mB n P _ ν _ raw obs array hraw hobs harray y d hd hdisp
  obtain ⟨hsp,hamp,hL,_,_⟩ := H hc hr hs hq y
  let t := packetWidth c r₀ s y
  have ht : 0<t := packetWidth_pos hc hr hs y
  let A := C/t^4
  have hA : 0≤A := by dsimp [A]; positivity
  let m : MeasurableSpace Ω := MeasurableSpace.comap obs mB
  let : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := hobs.comap_le
  let f := fun z => rawPacketDensity g c r₀ s (raw z) y
  let v := fun z => rawPacketDensity g c r₀ s (array (obs z)) y
  let e := fun z => (A*d)*rawCount (Metric.closedBall y (2*t+d)) (array (obs z))
  have hgs : HasCompactSupport (g : Position → ℝ) := by
    apply HasCompactSupport.intro (K := Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro z hz
    apply hg
    simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
  have hfm : Integrable f P := hraw.integrable_comp_of_integrable
    (rawPacketDensity_integrable_configuration g.continuous hgs hc hr hs ν y)
  have hpm : Measurable (fun x : Configuration n => rawPacketDensity g c r₀ s x y) :=
    ((continuous_rawPacketDensity g.continuous hc hr hs).comp
      (continuous_id.prodMk (continuous_const (y := y)))).measurable
  have hvmeas : StronglyMeasurable[m] v :=
    (hpm.comp (harray.comp (Measurable.of_comap_le le_rfl : @Measurable Ω B m _ obs))).stronglyMeasurable
  have hemeas : StronglyMeasurable[m] e :=
    (measurable_const.mul ((measurable_rawCount measurableSet_closedBall).comp
      (harray.comp (Measurable.of_comap_le le_rfl : @Measurable Ω B m _ obs)))).stronglyMeasurable
  have hvi : Integrable v P := by
    apply Integrable.of_bound (hvmeas.mono hm).aestronglyMeasurable ((n:ℝ)*(C/t^3))
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _≤∑ _i : Fin n, C/t^3 := Finset.sum_le_sum (fun i _ => hamp _)
      _=_ := by simp
  have hei : Integrable e P := by
    apply Integrable.of_bound (hemeas.mono hm).aestronglyMeasurable ((A*d)*(n:ℝ))
    filter_upwards [] with z
    have hp : 0≤e z := mul_nonneg (mul_nonneg hA hd) (rawCount_nonneg _ _)
    rw [Real.norm_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left (rawCount_le_number _ _) (mul_nonneg hA hd)
  have hcomp : ∀ᵐ z ∂P, |f z-v z|≤e z := by
    filter_upwards [hdisp] with z hz
    obtain ⟨p,hp⟩ := hz
    apply kernel_sum_matching_permuted _ y hA hd ?_ hL (raw z) (array (obs z)) p hp
    intro u hu
    by_contra hn
    have hh := hsp u hn
    rw [norm_sub_rev] at hh
    linarith
  have HH := condExp_matching hm hfm hvi hei hvmeas hemeas hcomp
  have He := conditionalPacketDensity_eq_condExp P ν hraw hobs g.continuous hgs hc hr hs y
  filter_upwards [HH,He] with z hz he
  rw [he]
  exact hz

end NeutralAtom

end
open MeasureTheory
open scoped ENNReal ContDiff
namespace NeutralAtom

def configurationOrderSetoid (n : ℕ) : Setoid (Configuration n) where
  r x y := ∃ p : Equiv.Perm (Fin n), y = x ∘ p
  iseqv := {
    refl := fun _ => ⟨Equiv.refl _, rfl⟩
    symm := by
      rintro x y ⟨p,rfl⟩
      refine ⟨p.symm, ?_⟩
      funext i
      simp
    trans := by
      rintro x y z ⟨p,rfl⟩ ⟨q,rfl⟩
      exact ⟨q.trans p,rfl⟩ }

def UnorderedArray (n : ℕ) := Quotient (configurationOrderSetoid n)

def forgetOrder {n : ℕ} (x : Configuration n) : UnorderedArray n := Quotient.mk _ x

instance unorderedArrayMeasurable (n : ℕ) : MeasurableSpace (UnorderedArray n) :=
  MeasurableSpace.map forgetOrder inferInstance

theorem measurable_forgetOrder {n : ℕ} : Measurable (forgetOrder (n := n)) :=
  measurable_iff_le_map.mpr le_rfl

theorem forgetOrder_permutation {n : ℕ} (x : Configuration n) (p : Equiv.Perm (Fin n)) :
    forgetOrder (x ∘ p) = forgetOrder x := by
  apply Eq.symm
  exact Quotient.sound ⟨p,rfl⟩

abbrev ObservationNoise (n J : ℕ) := Fin J → Fin n → Fin 3 → ℝ
abbrev ObservationSample (n J : ℕ) := Configuration n × ObservationNoise n J

def allObservationNoiseLaw (n J : ℕ) : Measure (ObservationNoise n J) :=
  Measure.pi (fun _ : Fin J => Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))

instance allObservationNoiseLaw_probability (n J : ℕ) :
    IsProbabilityMeasure (allObservationNoiseLaw n J) := by
  unfold allObservationNoiseLaw
  infer_instance

def observationLaw {n : ℕ} (J : ℕ) (ν : Measure (Configuration n)) :
    Measure (ObservationSample n J) := ν.prod (allObservationNoiseLaw n J)

instance observationLaw_probability {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (observationLaw J ν) := by
  unfold observationLaw
  infer_instance

theorem observationLaw_rawProjection {n J : ℕ} (ν : Measure (Configuration n)) :
    MeasurePreserving Prod.fst (observationLaw J ν) ν := measurePreserving_fst

def observationNoiseVector (v : Fin 3 → ℝ) : Position :=
  ∑ a : Fin 3, v a • EuclideanSpace.single a 1

theorem observationNoiseVector_coordinate (v : Fin 3 → ℝ) (a : Fin 3) :
    observationNoiseVector v a = v a := by
  simp [observationNoiseVector, Pi.single_apply]

theorem continuous_observationNoiseVector : Continuous observationNoiseVector := by
  unfold observationNoiseVector
  exact continuous_finsetSum Finset.univ (fun a _ => (continuous_apply a).smul continuous_const)

def observedOrdered {n J : ℕ} (r : Fin J → ℝ) (j : Fin J)
    (sample : ObservationSample n J) : Configuration n :=
  fun i => sample.1 i + (r j)^(101/100 : ℝ) • observationNoiseVector (sample.2 j i)

def observedArray {n J : ℕ} (r : Fin J → ℝ) (j : Fin J)
    (sample : ObservationSample n J) : UnorderedArray n :=
  forgetOrder (observedOrdered r j sample)

theorem measurable_observedOrdered {n J : ℕ} (r : Fin J → ℝ) (j : Fin J) :
    Measurable (observedOrdered (n := n) r j) := by
  apply Measurable.of_eval
  intro i
  have hn : Measurable (fun sample : ObservationSample n J => sample.2 j i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)
  exact ((measurable_pi_apply i).comp measurable_fst).add
    ((continuous_observationNoiseVector.measurable.comp hn).const_smul ((r j)^(101/100 : ℝ)))

theorem measurable_observedArray {n J : ℕ} (r : Fin J → ℝ) (j : Fin J) :
    Measurable (observedArray (n := n) r j) :=
  measurable_forgetOrder.comp (measurable_observedOrdered r j)

def tailObservation {n J : ℕ} (r : Fin J → ℝ) (j : ℕ)
    (sample : ObservationSample n J) : Fin J → UnorderedArray n :=
  fun k => if j ≤ k.val then observedArray r k sample else forgetOrder 0

theorem measurable_tailObservation {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    Measurable (tailObservation (n := n) r j) := by
  apply Measurable.of_eval
  intro k
  by_cases hj : j ≤ k.val
  · simpa only [tailObservation, ite_eq_left hj] using measurable_observedArray r k
  · simpa only [tailObservation, ite_eq_right hj] using
      (measurable_const : Measurable (fun _ : ObservationSample n J => forgetOrder (0 : Configuration n)))

@[instance_reducible] def observationSigma {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    MeasurableSpace (ObservationSample n J) :=
  MeasurableSpace.comap (tailObservation r j) inferInstance

theorem observationSigma_le {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    observationSigma (n := n) r j ≤ (inferInstance : MeasurableSpace (ObservationSample n J)) :=
  measurable_iff_comap_le.mp (measurable_tailObservation r j)

def eraseEarlierArrays {n J : ℕ} (j : ℕ) (v : Fin J → UnorderedArray n) :
    Fin J → UnorderedArray n := fun k => if j ≤ k.val then v k else forgetOrder 0

theorem measurable_eraseEarlierArrays {n J : ℕ} (j : ℕ) :
    Measurable (eraseEarlierArrays (n := n) (J := J) j) := by
  apply Measurable.of_eval
  intro k
  by_cases hj : j ≤ k.val
  · simpa only [eraseEarlierArrays, ite_eq_left hj] using (measurable_pi_apply k)
  · simpa only [eraseEarlierArrays, ite_eq_right hj] using
      (measurable_const : Measurable (fun _ : Fin J → UnorderedArray n => forgetOrder (0 : Configuration n)))

theorem tailObservation_erase {n J : ℕ} (r : Fin J → ℝ) {i j : ℕ} (hij : i ≤ j) :
    tailObservation (n := n) r j = eraseEarlierArrays j ∘ tailObservation r i := by
  funext sample k
  by_cases hj : j ≤ k.val
  · simp only [tailObservation, eraseEarlierArrays, Function.comp_apply,
      ite_eq_left hj, ite_eq_left (hij.trans hj)]
  · simp only [tailObservation, eraseEarlierArrays, Function.comp_apply, ite_eq_right hj]

theorem observationSigma_antitone {n J : ℕ} (r : Fin J → ℝ) :
    Antitone (observationSigma (n := n) r) := by
  intro i j hij
  unfold observationSigma
  rw [tailObservation_erase r hij, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (measurable_eraseEarlierArrays j))

theorem observationSigma_trivial {n J : ℕ} (r : Fin J → ℝ) :
    observationSigma (n := n) r J = ⊥ := by
  have hh : tailObservation (n := n) r J = fun _ => fun _ => forgetOrder (0 : Configuration n) := by
    funext sample k
    simp only [tailObservation, ite_eq_right (not_le.mpr k.isLt)]
  unfold observationSigma
  rw [hh]
  apply le_antisymm _ bot_le
  exact measurable_iff_comap_le.mp measurable_const

end NeutralAtom

end

end OAI
