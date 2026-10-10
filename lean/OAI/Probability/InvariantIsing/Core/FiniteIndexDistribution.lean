import OAI.Probability.InvariantIsing.Spectral.PositiveSpectralLabels
import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralMeasure

namespace OAI

/-! The positive part of a finite random label has the same distribution. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Classical
namespace InvariantIsing

variable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

def finiteIndexWeight (P : Measure Ω) (g : Ω → A) (a : A) : ℝ :=
  P.real (g ⁻¹' {a})

lemma finiteIndexWeight_sum (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → A) (hg : Measurable g) : ∑ a, finiteIndexWeight P g a=1 := by
  have hh := sum_measureReal_preimage_singleton (μ := P) Finset.univ
    (f := g) (fun a _ => hg (measurableSet_singleton a))
  simpa only [finiteIndexWeight,Finset.coe_univ,preimage_univ,probReal_univ] using hh

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma ae_finiteIndexWeight_pos (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → A) :
    ∀ᵐ x ∂P, 0 < finiteIndexWeight P g (g x) := by
  have hi a : ∀ᵐ x ∂P, g x=a → 0 < finiteIndexWeight P g a := by
    by_cases hp : 0 < finiteIndexWeight P g a
    · exact Eventually.of_forall (fun _ _ => hp)
    · have hz : P (g ⁻¹' {a})=0 := (measureReal_eq_zero_iff).mp
        (le_antisymm (le_of_not_gt hp) measureReal_nonneg)
      filter_upwards [compl_mem_ae_iff.mpr hz] with x hx
      exact fun h => (hx h).elim
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact hx _ rfl

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma positiveIndexWeight (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → A) (fallback : {a // 0 < finiteIndexWeight P g a})
    (a : {a // 0 < finiteIndexWeight P g a}) :
    finiteIndexWeight P (positiveSpectralLabel (finiteIndexWeight P g) fallback ∘ g) a=
      finiteIndexWeight P g a := by
  apply measureReal_congr
  filter_upwards [ae_finiteIndexWeight_pos P g] with x hx
  simp only [Function.comp_apply,positiveSpectralLabel,dite_eq_left hx,
    mem_preimage,mem_singleton_iff]
  exact propext Subtype.ext_iff

lemma finiteIndex_map (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → A) (hg : Measurable g) (c : A → ℝ) :
    P.map (c ∘ g)=finiteSpectralMeasure (finiteIndexWeight P g) c := by
  have hc : Measurable c := measurable_of_finite c
  rw [← Measure.map_map hc hg,Measure.map_eq_sum P g hg,Measure.map_sum hc.aemeasurable]
  unfold finiteSpectralMeasure
  congr 1
  funext a
  rw [Measure.map_smul _ hc.aemeasurable,Measure.map_dirac,finiteIndexWeight,
    measureReal_def,ENNReal.ofReal_toReal (measure_ne_top P _)]

end InvariantIsing

end

end OAI
