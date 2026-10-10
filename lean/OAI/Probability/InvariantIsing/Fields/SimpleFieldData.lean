import OAI.Probability.InvariantIsing.Core.FiniteIndexDistribution
import OAI.Probability.InvariantIsing.Spectral.CompactSpectralPartition
import OAI.Probability.InvariantIsing.Spectral.MeasureMagneticTransport
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

namespace OAI

/-! A simple random field is represented using only its positive-mass values. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Classical
namespace InvariantIsing

variable {Ω : Type*} [MeasurableSpace Ω]

def simpleFieldIndex (s : SimpleFunc Ω ℝ) (x : Ω) : s.range :=
  ⟨s x,s.mem_range_self x⟩

lemma measurable_simpleFieldIndex (s : SimpleFunc Ω ℝ) : Measurable (simpleFieldIndex s) :=
  s.measurable.subtype_mk

def simpleFieldWeight (P : Measure Ω) (s : SimpleFunc Ω ℝ) :=
  finiteIndexWeight P (simpleFieldIndex s)

abbrev SimpleFieldPositive (P : Measure Ω) (s : SimpleFunc Ω ℝ) :=
  {i : s.range // 0 < simpleFieldWeight P s i}

lemma simpleFieldWeight_sum (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) :
    ∑ i, simpleFieldWeight P s i=1 :=
  finiteIndexWeight_sum P _ (measurable_simpleFieldIndex s)

instance simpleFieldPositive_nonempty (P : Measure Ω) [IsProbabilityMeasure P]
    (s : SimpleFunc Ω ℝ) : Nonempty (SimpleFieldPositive P s) := by
  obtain ⟨i,hi⟩ := exists_pos_spectral_weight (fun _ => measureReal_nonneg) (simpleFieldWeight_sum P s)
  exact ⟨⟨i,hi⟩⟩

def simpleFieldPositiveIndex (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) :
    Ω → SimpleFieldPositive P s :=
  positiveSpectralLabel (simpleFieldWeight P s) (Classical.choice inferInstance) ∘ simpleFieldIndex s

lemma measurable_simpleFieldPositiveIndex (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) :
    Measurable (simpleFieldPositiveIndex P s) :=
  (measurable_of_finite _).comp (measurable_simpleFieldIndex s)

def simpleFieldValue (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ)
    (R : ℝ → ℝ) : ℝ :=
  (finiteMagneticFunctional R (fun i : SimpleFieldPositive P s => simpleFieldWeight P s i)
    (fun i => i.val.val)).toReal

lemma simpleFieldPositiveIndex_weight (P : Measure Ω) [IsProbabilityMeasure P]
    (s : SimpleFunc Ω ℝ) (i : SimpleFieldPositive P s) :
    finiteIndexWeight P (simpleFieldPositiveIndex P s) i=simpleFieldWeight P s i :=
  positiveIndexWeight P (simpleFieldIndex s) _ i

lemma simpleFieldPositiveIndex_ae (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) :
    (fun x => (simpleFieldPositiveIndex P s x).val.val) =ᵐ[P] s := by
  filter_upwards [ae_finiteIndexWeight_pos P (simpleFieldIndex s)] with x hx
  change 0 < simpleFieldWeight P s (simpleFieldIndex s x) at hx
  change (positiveSpectralLabel (simpleFieldWeight P s) _ (simpleFieldIndex s x)).val.val=s x
  rw [positiveSpectralLabel,dite_eq_left hx]
  rfl

lemma simpleField_law (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) :
    P.map s=finiteSpectralMeasure
      (fun i : SimpleFieldPositive P s => simpleFieldWeight P s i) (fun i => i.val.val) := by
  rw [← Measure.map_congr (simpleFieldPositiveIndex_ae P s)]
  have hh := finiteIndex_map P _ (measurable_simpleFieldPositiveIndex P s)
    (fun i : SimpleFieldPositive P s => i.val.val)
  have hw : finiteIndexWeight P (simpleFieldPositiveIndex P s)=
      (fun i : SimpleFieldPositive P s => simpleFieldWeight P s i) := funext (simpleFieldPositiveIndex_weight P s)
  rw [hw] at hh
  exact hh

lemma simpleField_integrable (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) :
    Integrable s P := by
  apply s.integrable_of_isFiniteMeasure

end InvariantIsing

end

end OAI
