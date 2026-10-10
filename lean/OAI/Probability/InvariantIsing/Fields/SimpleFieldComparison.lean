import OAI.Probability.InvariantIsing.Fields.SimpleFieldData
import OAI.Probability.InvariantIsing.Core.FiniteIndexMagnetic
import OAI.Probability.InvariantIsing.Spectral.MeasureMagneticLawInvariance

namespace OAI

/-! Law invariance and the integral transportation bound for simple fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
namespace InvariantIsing

variable (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)

include hcompact hbound ha hb

lemma simpleFieldValue_eq_of_map_eq {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (s : SimpleFunc Ω ℝ) (t : SimpleFunc Ξ ℝ) (he : P.map s=Q.map t) :
    simpleFieldValue P s (measureR (ν : Measure ℝ) b)=
      simpleFieldValue Q t (measureR (ν : Measure ℝ) b) := by
  apply measureMagnetic_eq_of_field_law_eq ν a b hcompact hbound ha hb
    (fun i : SimpleFieldPositive P s => simpleFieldWeight P s i) (fun i => i.val.val)
    (fun i : SimpleFieldPositive Q t => simpleFieldWeight Q t i) (fun i => i.val.val)
    (fun i => i.property) (fun i => i.property)
    (positiveSpectralWeights_sum _ (fun _ => measureReal_nonneg) (simpleFieldWeight_sum P s))
    (positiveSpectralWeights_sum _ (fun _ => measureReal_nonneg) (simpleFieldWeight_sum Q t))
  rw [← simpleField_law P s,← simpleField_law Q t,he]

lemma simpleFieldValue_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s t : SimpleFunc Ω ℝ) :
    simpleFieldValue P s (measureR (ν : Measure ℝ) b)-
      simpleFieldValue P t (measureR (ν : Measure ℝ) b) ≤ ∫ x, |s x-t x| ∂P := by
  have hh := finiteIndex_magnetic_sub_le P (simpleFieldPositiveIndex P s)
    (simpleFieldPositiveIndex P t) (measurable_simpleFieldPositiveIndex P s)
    (measurable_simpleFieldPositiveIndex P t) (fun i => i.val.val) (fun i => i.val.val)
    (fun i => by rw [simpleFieldPositiveIndex_weight]; exact i.property)
    ν a b hcompact hbound ha hb
  have hsw := funext (simpleFieldPositiveIndex_weight P s)
  have htw := funext (simpleFieldPositiveIndex_weight P t)
  rw [hsw,htw] at hh
  change simpleFieldValue P s _-simpleFieldValue P t _ ≤ _ at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [simpleFieldPositiveIndex_ae P s,simpleFieldPositiveIndex_ae P t] with x hs ht
  rw [hs,ht]

lemma simpleFieldValue_abs_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s t : SimpleFunc Ω ℝ) :
    |simpleFieldValue P s (measureR (ν : Measure ℝ) b)-
      simpleFieldValue P t (measureR (ν : Measure ℝ) b)| ≤ ∫ x, |s x-t x| ∂P := by
  have h1 := simpleFieldValue_sub_le ν a b hcompact hbound ha hb P s t
  have h2 := simpleFieldValue_sub_le ν a b hcompact hbound ha hb P t s
  simp_rw [abs_sub_comm (t _) (s _)] at h2
  exact abs_le.mpr ⟨by linarith,h1⟩

end InvariantIsing

end

end OAI
