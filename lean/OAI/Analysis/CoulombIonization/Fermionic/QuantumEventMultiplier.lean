import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Multiplier2
import OAI.Analysis.CoulombIonization.Localization.ObservationIntegral
import OAI.Analysis.CoulombIonization.Localization.ArraySymmetry

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

def quantumEventMultiplier {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (p : ℝ) : FermionLipschitzMultiplier N where
  value x := (Real.sqrt p)⁻¹ * Real.sqrt (quantumEventLikelihood b s x)
  constant := ‖(Real.sqrt p)⁻¹‖₊ *
    (sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b * ‖flattenConfiguration N‖₊)
  lipschitz := (lipschitzWith_smul ((Real.sqrt p)⁻¹)).comp
    ((sqrtArrayLikelihood_lipschitz b hs).comp (flattenConfiguration N).lipschitzWith)
  bound := ⟨(Real.sqrt p)⁻¹, fun x => by
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (Real.sqrt p)⁻¹ * 1 := mul_le_mul_of_nonneg_left
        (by simpa using Real.sqrt_le_sqrt (quantumEventLikelihood_le_one b hs x))
        (by positivity)
      _ = _ := mul_one _⟩
  symmetric π x := by rw [quantumEventLikelihood_symmetric b hs hsy π x]

@[simp] lemma quantumEventMultiplier_value {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (p : ℝ) (x : Configuration N) :
    (quantumEventMultiplier b hs hsy p).value x =
      (Real.sqrt p)⁻¹ * Real.sqrt (quantumEventLikelihood b s x) := rfl

lemma quantumEventMultiplier_sq {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) {p : ℝ} (hp : 0 < p) (x : Configuration N) :
    (quantumEventMultiplier b hs hsy p).value x ^ 2 =
      p⁻¹ * quantumEventLikelihood b s x := by
  rw [quantumEventMultiplier_value, mul_pow, inv_pow, Real.sq_sqrt hp.le,
    Real.sq_sqrt (quantumEventLikelihood_nonneg b hs x)]

lemma quantumEventMultiplier_lineDeriv {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (p : ℝ) (x : Configuration N) (i : Fin N) (a : Fin 3) :
    lineDeriv ℝ (quantumEventMultiplier b hs hsy p).value x (direction i a) =
      (Real.sqrt p)⁻¹ * lineDeriv ℝ (fun y => Real.sqrt (arrayLikelihood b s y))
        (flattenConfiguration N x) (Pi.single (i,a) 1) := by
  change deriv (fun t => (Real.sqrt p)⁻¹ *
    Real.sqrt (quantumEventLikelihood b s (x + t • direction i a))) 0 = _
  rw [deriv_const_mul_field]
  exact congrArg ((Real.sqrt p)⁻¹ * ·)
    (lineDeriv_flattenConfiguration (fun y => Real.sqrt (arrayLikelihood b s y)) x i a)

lemma quantumEventMultiplier_fisher {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) {p : ℝ} (hp : 0 < p) (x : Configuration N) :
    (∑ q : Fin N × Fin 3,
      (lineDeriv ℝ (quantumEventMultiplier b hs hsy p).value x (direction q.1 q.2))^2) =
    p⁻¹ * arrayFisher b s (flattenConfiguration N x) := by
  simp only [quantumEventMultiplier_lineDeriv, mul_pow, inv_pow, Real.sq_sqrt hp.le,
    arrayFisher, mul_sum]

lemma quantumEventMultiplier_fisher_integral {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (hp : 0 < quantumEventProbability F b s) :
    (∫ x, ∑ q : Fin N × Fin 3,
      (lineDeriv ℝ (quantumEventMultiplier b hs hsy (quantumEventProbability F b s)).value x
        (direction q.1 q.2))^2 ∂graphRawLaw F) ≤
      observationFisherConstant * (∑ j, (b j)^2) *
        (Real.log (Real.exp 1/quantumEventProbability F b s))^5 := by
  let := flatRawLaw_probability F hn
  simp only [quantumEventMultiplier_fisher b hs hsy hp]
  rw [integral_const_mul, ← integral_map (flattenConfiguration N).measurable.aemeasurable
    (arrayFisher_measurable b hs).aestronglyMeasurable]
  have hp' := hp
  rw [quantumEventProbability_eq_flat F b hs] at hp'
  have hh := arrayFisher_integral_log b hs (flatRawLaw F) hp'
  rw [← quantumEventProbability_eq_flat F b hs] at hh
  calc
    _ ≤ (quantumEventProbability F b s)⁻¹ *
        (observationFisherConstant * (∑ j, (b j)^2) *
          (Real.log (Real.exp 1/quantumEventProbability F b s))^5 *
            quantumEventProbability F b s) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp

end CoulombAtom

end

end OAI
