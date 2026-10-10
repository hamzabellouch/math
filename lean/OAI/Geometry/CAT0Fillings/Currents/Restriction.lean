import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.CanonicalMass
import OAI.Geometry.CAT0Fillings.Currents.WeightedAction

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
namespace BorelRestriction
open BorelCoefficients MassMeasure

universe u

variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ} {T : Functional X k}
noncomputable def restrictCurrent (hT : IsMetricCurrent T) (E : Set X) : Functional X k :=
  fun b π => if Admissible b π then
    borelAction (currentMassMeasure hT) hT (E.indicator b) π else 0

lemma restrictCurrent_apply (hT : IsMetricCurrent T) (E : Set X) {b : X → ℝ}
    {π : Fin k → X → ℝ} (h : Admissible b π) :
    restrictCurrent hT E b π = borelAction (currentMassMeasure hT) hT (E.indicator b) π :=
  ite_eq_left h

lemma restrictCurrent_isMetricCurrent (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) : IsMetricCurrent (restrictCurrent hT E) := by
  have he : restrictCurrent hT E =
      weightedCurrent (currentMassMeasure hT) hT (E.indicator (fun _ => 1)) := by
    funext b π
    dsimp only [restrictCurrent, weightedCurrent]
    congr 2
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [he]
  apply weightedCurrent_isMetricCurrent _ hT (currentMassMeasure_controls hT)
    ((integrable_const (1 : ℝ)).indicator hE) (M := 1)
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ E <;> simp [hx]

lemma restrictCurrent_controls (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) : Controls (restrictCurrent hT E) ((currentMassMeasure hT).restrict E) := by
  intro b π hb hπ
  rw [restrictCurrent_apply hT E ⟨hb, fun i => ⟨1, hπ i⟩⟩]
  have h := borelAction_bound (currentMassMeasure hT) hT (currentMassMeasure_controls hT)
    ((integrable_boundedLip _ hb).indicator hE) π (fun _ => 1) hπ
  simp only [NNReal.coe_one, Finset.prod_const_one, one_mul] at h
  apply h.trans_eq
  rw [← integral_indicator hE]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ E <;> simp [hx]

lemma restrictCurrent_complement_sum (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) (b : X → ℝ) (π : Fin k → X → ℝ) :
    restrictCurrent hT E b π + restrictCurrent hT Eᶜ b π = T b π := by
  by_cases h : Admissible b π
  · rw [restrictCurrent_apply hT E h, restrictCurrent_apply hT Eᶜ h,
      ← borelAction_add (currentMassMeasure hT) hT
        ((integrable_boundedLip _ h.1).indicator hE)
        ((integrable_boundedLip _ h.1).indicator hE.compl) π h.2]
    have he : E.indicator b + Eᶜ.indicator b = b := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [he]
    exact borelAction_eq _ hT (currentMassMeasure_controls hT) h
  · simp only [restrictCurrent, ite_eq_right h, hT.offDomain b π h, add_zero]

lemma restrictMass_le (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) ≤
      (currentMassMeasure hT).restrict E :=
  currentMassMeasure_le _ (restrictCurrent_controls hT hE)

lemma controls_restriction_sum (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    Controls T (currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) +
      currentMassMeasure (restrictCurrent_isMetricCurrent hT hE.compl)) := by
  intro b π hb hπ
  rw [← restrictCurrent_complement_sum hT hE b π]
  apply (abs_add_le _ _).trans
  rw [integral_add_measure (integrable_boundedLip _ hb).abs (integrable_boundedLip _ hb).abs]
  exact add_le_add (currentMassMeasure_controls (restrictCurrent_isMetricCurrent hT hE) b π hb hπ)
    (currentMassMeasure_controls (restrictCurrent_isMetricCurrent hT hE.compl) b π hb hπ)

lemma restriction_massMeasure (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) =
      (currentMassMeasure hT).restrict E := by
  apply le_antisymm (restrictMass_le hT hE)
  rw [Measure.le_iff]
  intro B hB
  let μ := currentMassMeasure hT
  let ν := currentMassMeasure (restrictCurrent_isMetricCurrent hT hE)
  let ξ := currentMassMeasure (restrictCurrent_isMetricCurrent hT hE.compl)
  have hle : μ ≤ ν + ξ := currentMassMeasure_le hT (controls_restriction_sum hT hE)
  have hξ : ξ (B ∩ E) = 0 := by
    apply le_antisymm _ bot_le
    apply (restrictMass_le hT hE.compl (B ∩ E)).trans
    rw [Measure.restrict_apply (hB.inter hE)]
    have he : B ∩ E ∩ Eᶜ = ∅ := by aesop
    rw [he, measure_empty]
    exact le_refl _
  rw [Measure.restrict_apply hB]
  calc
    μ (B ∩ E) ≤ (ν + ξ) (B ∩ E) := hle _
    _ = ν (B ∩ E) := by rw [Measure.add_apply, hξ, add_zero]
    _ ≤ ν B := measure_mono inter_subset_left

lemma restriction_mass (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    mass (restrictCurrent hT E) = (currentMassMeasure hT).real E := by
  rw [← currentMassMeasure_total (restrictCurrent_isMetricCurrent hT hE),
    Measure.real, restriction_massMeasure hT hE, Measure.restrict_apply_univ]
  rfl

end BorelRestriction

attribute [local instance] Classical.propDecidable
end CAT0Fillings
end

end OAI
