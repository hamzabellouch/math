import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.QuantumEventTilt

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombObservation

def dyadicObservationWidth (r : ℝ) (k : ℕ) : ℝ := ((2:ℝ)^k * r)^(1.01:ℝ)

lemma dyadicObservationWidth_pos {r : ℝ} (hr : 0 < r) (k : ℕ) :
    0 < dyadicObservationWidth r k := Real.rpow_pos_of_pos (by positivity) _

lemma dyadicObservationWidth_inv_sq {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (dyadicObservationWidth r k)⁻¹^2 =
      r^(-2.02:ℝ) * ((2:ℝ)^(-2.02:ℝ))^k := by
  unfold dyadicObservationWidth
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity), ← Real.rpow_mul (by positivity)]
  norm_num
  rw [Real.mul_rpow (by positivity) hr.le, ← Real.rpow_pow_comm (by norm_num)]
  ring

lemma dyadicObservationRatio_nonneg : 0 ≤ (2:ℝ)^(-2.02:ℝ) := Real.rpow_nonneg (by norm_num) _

lemma dyadicObservationRatio_le_half : (2:ℝ)^(-2.02:ℝ) ≤ 1/2 := by
  calc
    _ ≤ (2:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = _ := by norm_num

lemma geometric_sum_le_two {q : ℝ} (hq : 0 ≤ q) (hq2 : q ≤ 1/2) (K : ℕ) :
    (∑ k ∈ range K, q^k) ≤ 2 := by
  have hh (n : ℕ) : (∑ k ∈ range n, q^k) ≤ 2 * (1-q^n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, pow_succ]
      nlinarith [pow_nonneg hq n, mul_le_mul_of_nonneg_right hq2 (pow_nonneg hq n)]
  exact (hh K).trans (by nlinarith [pow_nonneg hq K])

lemma dyadicObservation_inv_sq_sum {r : ℝ} (hr : 0 < r) (K : ℕ) :
    (∑ k : Fin K, (dyadicObservationWidth r k)⁻¹^2) ≤ 2*r^(-2.02:ℝ) := by
  simp only [dyadicObservationWidth_inv_sq hr]
  rw [← mul_sum, Fin.sum_univ_eq_sum_range]
  have hh := mul_le_mul_of_nonneg_left
    (geometric_sum_le_two dyadicObservationRatio_nonneg dyadicObservationRatio_le_half K)
    (Real.rpow_nonneg hr.le (-2.02))
  simpa only [mul_comm] using hh

end CoulombObservation
namespace CoulombAtom
open CoulombObservation

theorem quantum_dyadic_observation_event_tilt {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z N)
    {r : ℝ} (hr : 0 < r) (K : ℕ)
    {s : Set (Fin K × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s)
    (hp : 0 < quantumEventProbability F (fun k : Fin K => (dyadicObservationWidth r k)⁻¹) s) :
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G =
        (ENNReal.ofReal (quantumEventProbability F
          (fun k : Fin K => (dyadicObservationWidth r k)⁻¹) s))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (quantumObservationEvent (fun k : Fin K => (dyadicObservationWidth r k)⁻¹) s)) ∧
      formEnergy Z (graphFormVector G) ≤ energy Z N +
        observationFisherConstant * r^(-2.02:ℝ) *
          (Real.log (Real.exp 1/quantumEventProbability F
            (fun k : Fin K => (dyadicObservationWidth r k)⁻¹) s))^5 := by
  let b : Fin K → ℝ := fun k => (dyadicObservationWidth r k)⁻¹
  obtain ⟨G,hnG,hlaw,hE⟩ := quantum_observation_event_tilt hZ F hn hF b hs hsy hp
  refine ⟨G,hnG,hlaw,hE.trans ?_⟩
  have hp1 : quantumEventProbability F b s ≤ 1 := by
    let := graphRawLaw_probability F hn
    have hi := integrable_bounded_probability (μ := graphRawLaw F)
      (quantumEventLikelihood_measurable b hs) (quantumEventLikelihood_nonneg b hs)
      (quantumEventLikelihood_le_one b hs)
    have hh := integral_mono hi (integrable_const (1:ℝ)) (quantumEventLikelihood_le_one b hs)
    simpa [quantumEventProbability] using hh
  have hlog : 0 ≤ (Real.log (Real.exp 1/quantumEventProbability F b s))^5 := by
    apply pow_nonneg
    rw [eventLog_eq hp]
    have h := Real.log_nonpos hp.le hp1
    linarith
  have hsum := dyadicObservation_inv_sq_sum hr K
  have hC := observationFisherConstant_pos
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum (show 0 ≤ observationFisherConstant/2 by positivity)) hlog
  apply add_le_add_right
  calc
    _ ≤ _ := hh
    _ = _ := by ring

end CoulombAtom

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombObservation

def scaleObservationArray {J I : Type*} [Fintype J] [Fintype I]
    (ell : J → ℝ) : (J × I → ℝ) →L[ℝ] (J × I → ℝ) :=
  ContinuousLinearMap.pi (fun q => ell q.1 • ContinuousLinearMap.proj q)

@[simp] lemma scaleObservationArray_apply {J I : Type*} [Fintype J] [Fintype I]
    (ell : J → ℝ) (u : J × I → ℝ) (q : J × I) :
    scaleObservationArray ell u q = ell q.1 * u q := rfl

lemma scaleObservationArray_reindex {J I : Type*} [Fintype J] [Fintype I]
    (ell : J → ℝ) (e : Equiv.Perm I) (u : J × I → ℝ) :
    scaleObservationArray ell (arrayReindex e u) = arrayReindex e (scaleObservationArray ell u) := by
  ext q
  simp only [scaleObservationArray_apply, arrayReindex_apply]

end CoulombObservation
namespace CoulombAtom
open CoulombObservation

def physicalObservationArray {N : ℕ} {J : Type*} [Fintype J]
    (ell : J → ℝ) (z : Configuration N × (J × (Fin N × Fin 3) → ℝ)) :
    J × (Fin N × Fin 3) → ℝ := fun q => z.1 q.2.1 q.2.2 + ell q.1 * z.2 q

def physicalObservationEvent {N : ℕ} {J : Type*} [Fintype J]
    (ell : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) :
    Set (Configuration N × (J × (Fin N × Fin 3) → ℝ)) :=
  physicalObservationArray ell ⁻¹' s

def physicalObservationProbability {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (ell : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) : ℝ :=
  (((graphRawLaw F).prod (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw)))
    (physicalObservationEvent ell s)).toReal

lemma physicalObservationEvent_eq {N : ℕ} {J : Type*} [Fintype J]
    (ell : J → ℝ) (hell : ∀ j, 0 < ell j) (s : Set (J × (Fin N × Fin 3) → ℝ)) :
    quantumObservationEvent (fun j => (ell j)⁻¹) (scaleObservationArray ell ⁻¹' s) =
      physicalObservationEvent ell s := by
  have he (z : Configuration N × (J × (Fin N × Fin 3) → ℝ)) :
      scaleObservationArray ell
        (observationPlacement (fun j => (ell j)⁻¹) (flattenConfiguration N z.1) + z.2) =
        physicalObservationArray ell z := by
    ext q
    simp only [scaleObservationArray_apply, Pi.add_apply, observationPlacement_apply,
      flattenConfiguration_apply, physicalObservationArray]
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ (hell q.1).ne', one_mul]
  ext z
  exact congrArg (· ∈ s) (he z) |>.to_iff

lemma scaledObservationEvent_symmetric {N : ℕ} {J : Type*} [Fintype J]
    (ell : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hsy : QuantumEventSymmetric s) :
    QuantumEventSymmetric (scaleObservationArray ell ⁻¹' s) := by
  intro π u
  change scaleObservationArray ell (arrayReindex (π.prodCongr (Equiv.refl (Fin 3))) u) ∈ s ↔
    scaleObservationArray ell u ∈ s
  rw [scaleObservationArray_reindex]
  exact hsy π _

lemma quantumEventProbability_eq_physical {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (ell : J → ℝ) (hell : ∀ j, 0 < ell j)
    {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s) :
    quantumEventProbability F (fun j => (ell j)⁻¹) (scaleObservationArray ell ⁻¹' s) =
      physicalObservationProbability F ell s := by
  have he := quantumEventProbability_ofReal F hn (fun j => (ell j)⁻¹)
    (hs.preimage (scaleObservationArray ell).measurable)
  rw [physicalObservationEvent_eq ell hell] at he
  have hp : 0 ≤ quantumEventProbability F (fun j => (ell j)⁻¹)
      (scaleObservationArray ell ⁻¹' s) :=
    integral_nonneg (quantumEventLikelihood_nonneg _ (hs.preimage (scaleObservationArray (I := Fin N × Fin 3) ell).measurable))
  exact (ENNReal.toReal_ofReal hp).symm.trans (congrArg ENNReal.toReal he)

theorem quantum_physical_observation_event_tilt {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z N)
    {J : Type*} [Fintype J] (ell : J → ℝ) (hell : ∀ j, 0 < ell j)
    {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (hp : 0 < physicalObservationProbability F ell s) :
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G =
        (ENNReal.ofReal (physicalObservationProbability F ell s))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (physicalObservationEvent ell s)) ∧
      formEnergy Z (graphFormVector G) ≤ energy Z N +
        (observationFisherConstant/2) * (∑ j, ((ell j)⁻¹)^2) *
          (Real.log (Real.exp 1/physicalObservationProbability F ell s))^5 := by
  have hm := hs.preimage (scaleObservationArray ell).measurable
  have hp' : 0 < quantumEventProbability F (fun j => (ell j)⁻¹)
      (scaleObservationArray ell ⁻¹' s) := by
    rwa [quantumEventProbability_eq_physical F hn ell hell hs]
  obtain ⟨G, hG, hlaw, hE⟩ := quantum_observation_event_tilt hZ F hn hF
    (fun j => (ell j)⁻¹) hm (scaledObservationEvent_symmetric ell hsy) hp'
  rw [quantumEventProbability_eq_physical F hn ell hell hs,
    physicalObservationEvent_eq ell hell] at hlaw
  rw [quantumEventProbability_eq_physical F hn ell hell hs] at hE
  exact ⟨G,hG,hlaw,hE⟩

theorem quantum_physical_dyadic_event_tilt {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (hF : formEnergy Z (graphFormVector F) = energy Z N)
    {r : ℝ} (hr : 0 < r) (K : ℕ)
    {s : Set (Fin K × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s)
    (hp : 0 < physicalObservationProbability F (fun k : Fin K => dyadicObservationWidth r k) s) :
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G =
        (ENNReal.ofReal (physicalObservationProbability F
          (fun k : Fin K => dyadicObservationWidth r k) s))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (physicalObservationEvent (fun k : Fin K => dyadicObservationWidth r k) s)) ∧
      formEnergy Z (graphFormVector G) ≤ energy Z N +
        observationFisherConstant * r^(-2.02:ℝ) *
          (Real.log (Real.exp 1/physicalObservationProbability F
            (fun k : Fin K => dyadicObservationWidth r k) s))^5 := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  have hell : ∀ k, 0 < ell k := fun k => dyadicObservationWidth_pos hr k
  have hm := hs.preimage (scaleObservationArray ell).measurable
  have hp' : 0 < quantumEventProbability F (fun k : Fin K => (dyadicObservationWidth r k)⁻¹)
      (scaleObservationArray ell ⁻¹' s) := by
    rwa [quantumEventProbability_eq_physical F hn ell hell hs]
  obtain ⟨G,hG,hlaw,hE⟩ := quantum_dyadic_observation_event_tilt hZ F hn hF hr K hm
    (scaledObservationEvent_symmetric ell hsy) hp'
  rw [quantumEventProbability_eq_physical F hn ell hell hs,
    physicalObservationEvent_eq ell hell] at hlaw
  rw [quantumEventProbability_eq_physical F hn ell hell hs] at hE
  exact ⟨G,hG,hlaw,hE⟩

end CoulombAtom

end

end OAI
