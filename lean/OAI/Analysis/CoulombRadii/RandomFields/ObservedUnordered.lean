import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalMatching

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace NeutralAtom

def unorderedSum {n : ℕ} (f : Position → ℝ) : UnorderedArray n → ℝ :=
  Quotient.lift (fun x : Configuration n => ∑ i, f (x i)) (by
    rintro x y ⟨p,rfl⟩
    exact (Equiv.sum_comp p (fun i => f (x i))).symm)

@[simp] theorem unorderedSum_forgetOrder {n : ℕ} (f : Position → ℝ) (x : Configuration n) :
    unorderedSum f (forgetOrder x)=∑ i, f (x i) := rfl

lemma measurable_unorderedSum {n : ℕ} {f : Position → ℝ} (hf : Measurable f) :
    Measurable (unorderedSum (n := n) f) := by
  intro s hs
  change MeasurableSet ((fun x : Configuration n => ∑ i, f (x i)) ⁻¹' s)
  exact (Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))) hs

lemma unorderedSum_bound {n : ℕ} (f : Position → ℝ) {M : ℝ}
    (hf : ∀ x, |f x|≤M) (v : UnorderedArray n) : |unorderedSum f v|≤(n:ℝ)*M := by
  induction v using Quotient.inductionOn with | h x =>
    change |∑ i, f (x i)|≤_
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun i _ => hf (x i))).trans_eq (by simp))

lemma observationNoiseLaw_ae_support : ∀ᵐ u ∂observationNoiseLaw, |u|<1 := by
  rw [observationNoiseLaw,ae_withDensity_iff observationNoiseDensity_contDiff.continuous.measurable.ennreal_ofReal]
  filter_upwards [] with u hu
  by_contra hn
  apply hu
  simp [observationNoiseDensity_formula,hn]

lemma allObservationNoiseLaw_ae_support (n J : ℕ) :
    ∀ᵐ u ∂allObservationNoiseLaw n J, ∀ j i a, |u j i a|<1 := by
  simp only [ae_all_iff]
  intro j i a
  exact ((measurePreserving_eval (fun _ : Fin 3 => observationNoiseLaw) a).comp
    ((measurePreserving_eval (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)) i).comp
      (measurePreserving_eval (fun _ : Fin J => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw))) j))).quasiMeasurePreserving.ae observationNoiseLaw_ae_support

lemma observationNoiseVector_norm_le {v : Fin 3 → ℝ} (hv : ∀ a, |v a|≤1) :
    ‖observationNoiseVector v‖≤Real.sqrt 3 := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  calc
    _≤∑ _a : Fin 3, (1:ℝ) := Finset.sum_le_sum (fun a _ => by
      rw [observationNoiseVector_coordinate]
      nlinarith [(abs_le.mp (hv a)).1,(abs_le.mp (hv a)).2])
    _=_ := by norm_num

lemma observationLaw_ae_displacement {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] (r : Fin J → ℝ) (hR : ∀ k, 0≤r k) :
    ∀ᵐ z ∂observationLaw J ν, ∀ j i,
      ‖z.1 i-observedOrdered r j z i‖≤Real.sqrt 3*(r j)^(101/100:ℝ) := by
  have hh : ∀ᵐ z ∂observationLaw J ν, ∀ j i a, |z.2 j i a|<1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae (allObservationNoiseLaw_ae_support n J)
  filter_upwards [hh] with z hz j i
  have hn := observationNoiseVector_norm_le (fun a => (hz j i a).le)
  rw [observedOrdered,sub_add_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (hR j) _)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (hR j) _)

lemma unorderedSum_tail_stronglyMeasurable {n J : ℕ} (r : Fin J → ℝ) (j : ℕ)
    (k : Fin J) {f : Position → ℝ} (hf : Measurable f) :
    StronglyMeasurable[observationSigma (n := n) r j]
      (fun z => unorderedSum f (tailObservation r j z k)) :=
  ((measurable_unorderedSum hf).comp ((measurable_pi_apply k).comp
    (comap_measurable (tailObservation r j)))).stronglyMeasurable

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

theorem physical_posterior_kernel_matching (g : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hgn : (∫ z, g z^2)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ {c r₀ s : ℝ}, 0<c → 0<r₀ → 0<s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ {n J : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
      (r : Fin J → ℝ), (∀ k, 0≤r k) → ∀ {j : ℕ} (k : Fin J), j≤k.val → ∀ y : Position,
    ∀ᵐ z ∂observationLaw J ν,
      |conditionalPacketDensity (observationLaw J ν) Prod.fst (tailObservation r j)
          g c r₀ s (tailObservation r j z) y-
        rawPacketDensity g c r₀ s (observedOrdered r k z) y|≤
      (C/(packetWidth c r₀ s y)^4*(Real.sqrt 3*(r k)^(101/100:ℝ)))*
        rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+Real.sqrt 3*(r k)^(101/100:ℝ)))
          (observedOrdered r k z) := by
  obtain ⟨C,hC,H⟩ := master_kernel_estimates g hg hgn
  refine ⟨C,hC,?_⟩
  intro c r₀ s hc hr hs hq n J ν _ r hR j k hj y
  obtain ⟨hsp,hamp,hL,_,_⟩ := H hc hr hs hq y
  let P := observationLaw J ν
  let t := packetWidth c r₀ s y
  let d := Real.sqrt 3*(r k)^(101/100:ℝ)
  let A := C/t^4
  have hd : 0≤d := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hR k) _)
  have ht : 0<t := packetWidth_pos hc hr hs y
  have hA : 0≤A := by dsimp [A]; positivity
  let v := fun z : ObservationSample n J => rawPacketDensity g c r₀ s (observedOrdered r k z) y
  let e := fun z : ObservationSample n J => (A*d)*rawCount (Metric.closedBall y (2*t+d)) (observedOrdered r k z)
  have hvmeas : StronglyMeasurable[observationSigma r j] v := by
    have HH := unorderedSum_tail_stronglyMeasurable (n := n) r j k
      (((continuous_packetKernel g.continuous hc hr hs).comp
        (continuous_id.prodMk (continuous_const (y := y)))).measurable)
    simpa only [v,tailObservation,ite_eq_left hj,observedArray,unorderedSum_forgetOrder,rawPacketDensity,Function.comp_apply,id_eq] using HH
  have hemeas : StronglyMeasurable[observationSigma r j] e := by
    have HH := unorderedSum_tail_stronglyMeasurable (n := n) r j k
      (measurable_const.indicator (s := Metric.closedBall y (2*t+d)) measurableSet_closedBall :
        Measurable ((Metric.closedBall y (2*t+d)).indicator (fun _ => (1:ℝ))))
    have HHH := HH.const_mul (A*d)
    simpa only [e,tailObservation,ite_eq_left hj,observedArray,unorderedSum_forgetOrder,rawCount] using HHH
  have hgs : HasCompactSupport (g : Position → ℝ) := by
    apply HasCompactSupport.intro (K := Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro z hz
    apply hg
    simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
  have hf : Integrable (fun z : ObservationSample n J => rawPacketDensity g c r₀ s z.1 y) P :=
    (observationLaw_rawProjection ν).integrable_comp_of_integrable
      (rawPacketDensity_integrable_configuration g.continuous hgs hc hr hs ν y)
  have hv : Integrable v P := by
    apply Integrable.of_bound (hvmeas.mono (observationSigma_le _ _)).aestronglyMeasurable ((n:ℝ)*(C/t^3))
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun i _ => hamp (observedOrdered r k z i))).trans_eq (by simp [t]))
  have he : Integrable e P := by
    apply Integrable.of_bound (hemeas.mono (observationSigma_le _ _)).aestronglyMeasurable ((A*d)*(n:ℝ))
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hA hd) (rawCount_nonneg _ _))]
    exact mul_le_mul_of_nonneg_left (rawCount_le_number _ _) (mul_nonneg hA hd)
  have hcomp : ∀ᵐ z ∂P, |rawPacketDensity g c r₀ s z.1 y-v z|≤e z := by
    filter_upwards [observationLaw_ae_displacement ν r hR] with z hz
    apply kernel_sum_matching _ y hA hd ?_ hL z.1 (observedOrdered r k z) (hz k)
    intro u hu
    by_contra hn
    have hh := hsp u hn
    rw [norm_sub_rev] at hh
    linarith
  have HH := condExp_matching (observationSigma_le r j) hf hv he hvmeas hemeas hcomp
  have He := conditionalPacketDensity_eq_condExp (observationLaw J ν) ν
    (observationLaw_rawProjection ν) (measurable_tailObservation r j) g.continuous hgs hc hr hs y
  filter_upwards [HH,He] with z hz he
  rw [he]
  exact hz

end NeutralAtom

end

end OAI
