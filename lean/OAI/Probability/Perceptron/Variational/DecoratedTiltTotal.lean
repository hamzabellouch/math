import Mathlib
import OAI.Probability.Perceptron.Cascade.DecoratedWeightedTotal

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

omit [Nonempty S] in
lemma decoratedWeightedTotal_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (decoratedWeightedTotal step n F) := by
  have he : decoratedWeightedTotal step n F =
      fun p => cascadeTotal n (decoratedCascadeTransform step n F p) := by
    funext p; exact decoratedWeightedTotal_transform step hs n F hF p
  rw [he]
  exact (cascadeTotal_measurable n).comp (decoratedCascadeTransform_measurable step hs n F hF)

def decoratedBiasedLaw (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ) (x : X) (a : ℝ) :
    Measure (DecoratedCascade S n) :=
  normalizedMeasure ((decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)).withDensity
    (fun η => ENNReal.ofReal ((decoratedWeightedTotal step n F (x,η))^a)))

lemma decoratedWeightedTotal_pos (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)),
      0 < decoratedWeightedTotal step n F (x,η) :=
  (decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1 F hF hI hM x).symm.ae_snd
    measurableSet_Ioi (cascadeTotal_regular n z hz hz0 hz1).1

lemma decoratedLogTotalMoment_integrable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (x : X) (a : ℝ) (ha : ∀ i, a < z i) :
    Integrable (fun η => Real.exp (a*Real.log (decoratedWeightedTotal step n F (x,η))))
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  have hid := (decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1 F hF hI hM x).comp
    (Real.measurable_exp.comp (Real.measurable_log.const_mul a))
  exact hid.integrable_iff.mpr (cascadeLogTotalMoment_integrable n z hz hz0 hz1 a ha)

lemma decoratedLogTotalMoment_eq (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (a : ℝ) :
    (∫ η, Real.exp (a*Real.log (decoratedWeightedTotal step n F (x,η)))
      ∂decoratedCascadeLaw ν n z) =
      ∫ η, Real.exp (a*Real.log (cascadeTotal n η)) ∂cascadeLaw n z := by
  exact ((decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1 F hF hI hM x).comp
    (Real.measurable_exp.comp (Real.measurable_log.const_mul a))).integral_eq

lemma decoratedBiasedLaw_eq_exponentialTilt (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (a : ℝ) :
    decoratedBiasedLaw ν step n z F x a =
      exponentialMarkTilt (decoratedCascadeLaw ν n z) a
        (fun η => Real.log (decoratedWeightedTotal step n F (x,η))) := by
  unfold decoratedBiasedLaw exponentialMarkTilt
  congr 1
  apply withDensity_congr_ae
  filter_upwards [decoratedWeightedTotal_pos ν step hs n z hz hz0 hz1 F hF hI hM x] with η hη
  rw [Real.rpow_def_of_pos hη,mul_comm]

lemma decoratedBiasedLaw_probability (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (x : X) (a : ℝ) (ha : ∀ i, a < z i) :
    IsProbabilityMeasure (decoratedBiasedLaw ν step n z F x a) := by
  rw [decoratedBiasedLaw_eq_exponentialTilt ν step hs n z hz hz0 hz1 F hF hI hM x a]
  exact exponentialMarkTilt_probability _
    (decoratedLogTotalMoment_integrable ν step hs n z hz hz0 hz1 F hF hI hM x a ha)

def decoratedRootPotential (step : X×S → X) (n : ℕ) (F : Fin (n+1) → X×S → ℝ)
    (p : X×(S×DecoratedCascade S n)) : ℝ :=
  F 0 (p.1,p.2.1)+Real.log
    (decoratedWeightedTotal step n (fun i => F i.succ) (step (p.1,p.2.1),p.2.2))

omit [Nonempty S] in
lemma decoratedRootPotential_measurable (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable (decoratedRootPotential step n F) :=
  ((hF 0).comp (measurable_fst.prodMk measurable_snd.fst)).add
    (((decoratedWeightedTotal_measurable step hs n _ (fun i => hF i.succ)).comp
      ((hs.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)).log)

lemma decoratedRootPotential_integrable (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    Integrable (fun p => Real.exp (z 0*decoratedRootPotential step n F (x,p)))
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))) := by
  let ρ : Measure (DecoratedCascade S n) := decoratedCascadeLaw ν n (fun i => z i.succ)
  let θ : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
  let T : S×DecoratedCascade S n → StableCascade n := fun p =>
    decoratedCascadeTransform step n (fun i => F i.succ) (step (x,p.1),p.2)
  have hT : Measurable T := (decoratedCascadeTransform_measurable step hs n _
    (fun i => hF i.succ)).comp
      ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  have hLaw (s) : ρ.map (fun c => T (s,c)) = θ := by
    exact decoratedCascadeTransform_law ν step hs n (fun i => z i.succ)
      (fun i => hz0 i.succ) (fun i => hz1 i.succ) (fun i => F i.succ)
      (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ) (step (x,s))
  have hp : MeasurePreserving (fun p : S×DecoratedCascade S n => (p.1,T p))
      ((ν : Measure S).prod ρ) ((ν : Measure S).prod θ) :=
    ⟨measurable_fst.prodMk hT,descendant_transform_independent _ _ _ T hT hLaw⟩
  have htail := cascadeLogTotalMoment_integrable n (fun i => z i.succ)
    (fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)) (fun i => hz0 i.succ)
    (fun i => hz1 i.succ) (z 0) (fun i => hz (by simp))
  have hprod := (hI 0 x).mul_prod htail
  have he := (hp.integrable_comp hprod.aestronglyMeasurable).mpr hprod
  apply he.congr
  filter_upwards [] with p
  dsimp [Function.comp,T,decoratedRootPotential]
  rw [decoratedWeightedTotal_transform step hs n _ (fun i => hF i.succ),mul_add,Real.exp_add]

lemma decoratedWeightedTotal_succ_eq (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν (n+1) z : Measure (DecoratedCascade S (n+1))),
      decoratedWeightedTotal step (n+1) F (x,η) =
        poissonWeightedTotal (fun p => decoratedRootPotential step n F (x,p)) η := by
  have hT : Measurable (fun η : DecoratedCascade S (n+1) =>
      decoratedCascadeTransform step (n+1) F (x,η)) :=
    (decoratedCascadeTransform_measurable step hs (n+1) F hF).comp
      (measurable_const.prodMk measurable_id)
  have hp : MeasurePreserving (fun η => decoratedCascadeTransform step (n+1) F (x,η))
      (decoratedCascadeLaw ν (n+1) z : Measure (DecoratedCascade S (n+1))) (cascadeLaw (n+1) z) :=
    ⟨hT,decoratedCascadeTransform_law ν step hs (n+1) z hz0 hz1 F hF hI hM x⟩
  have htail := (cascadeTotal_regular n (fun i => z i.succ)
    (fun i j h => hz (Fin.succ_lt_succ_iff.mpr h))
    (fun i => hz0 i.succ) (fun i => hz1 i.succ)).1
  have hae := hp.quasiMeasurePreserving.ae (cascadeTotal_succ_eq z htail)
  have hreg := markedStable_regular
    ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ) : Measure (DecoratedCascade S n))) (hz0 0) (hz1 0)
  filter_upwards [hae,hreg] with η hη hr
  rw [decoratedWeightedTotal_transform step hs (n+1) F hF,hη]
  change poissonWeightedTotal (fun C => Real.log (cascadeTotal n C))
    ((markedStableCountKernel η).map (fun q : ℝ×(S×DecoratedCascade S n) =>
      (q.1+F 0 (x,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (x,q.2.1),q.2.2)))) = _
  rw [markedStableCountKernel_eq η hr.1 hr.2]
  have hmap : Measurable (fun q : ℝ×(S×DecoratedCascade S n) =>
      (q.1+F 0 (x,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (x,q.2.1),q.2.2))) :=
    (measurable_fst.add ((hF 0).comp (measurable_const.prodMk measurable_snd.fst))).prodMk
      ((decoratedCascadeTransform_measurable step hs n _ (fun i => hF i.succ)).comp
        ((hs.comp (measurable_const.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
  unfold poissonWeightedTotal
  have hobs : Measurable (fun p : ℝ×StableCascade n =>
      ENNReal.ofReal (Real.exp (p.1+Real.log (cascadeTotal n p.2)))) :=
    (measurable_fst.add ((cascadeTotal_measurable n).comp measurable_snd).log).exp.ennreal_ofReal
  rw [lintegral_map hobs hmap]
  congr 1
  apply lintegral_congr
  intro q
  dsimp [decoratedRootPotential]
  rw [decoratedWeightedTotal_transform step hs n _ (fun i => hF i.succ),add_assoc]

lemma decoratedBiasedLaw_succ_eq_weighted (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (a : ℝ) :
    decoratedBiasedLaw ν step (n+1) z F x a = weightedTotalBiasedLaw
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ))) a (z 0)
      (fun p => decoratedRootPotential step n F (x,p)) := by
  unfold decoratedBiasedLaw weightedTotalBiasedLaw
  congr 1
  apply withDensity_congr_ae
  filter_upwards [decoratedWeightedTotal_succ_eq ν step hs n z hz hz0 hz1 F hF hI hM x] with η hη
  rw [hη]

end SphericalPerceptronFreeEnergy

end

end OAI
