import OAI.Probability.InvariantIsing.Spectral.MeasureMagneticLawInvariance

namespace OAI

/-! The finite positive rational field laws used in the W1 extension of
the magnetic pressure formula. Labels may repeat the same field value. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

structure RationalFieldLaw where
  size : ℕ
  weight : Fin size → ℚ
  positive : ∀ i, 0 < weight i
  total : ∑ i, weight i=1
  field : Fin size → ℝ

namespace RationalFieldLaw

def mass (p : RationalFieldLaw) (i : Fin p.size) : ℝ := p.weight i

lemma mass_pos (p : RationalFieldLaw) (i : Fin p.size) : 0 < p.mass i := by
  change 0 < (p.weight i : ℝ)
  exact_mod_cast p.positive i

lemma mass_sum (p : RationalFieldLaw) : ∑ i, p.mass i=1 := by
  change (∑ i, (p.weight i : ℝ))=1
  exact_mod_cast p.total

def measure (p : RationalFieldLaw) : Measure ℝ := finiteSpectralMeasure p.mass p.field

instance probability (p : RationalFieldLaw) : IsProbabilityMeasure p.measure :=
  finiteSpectralMeasure_probability p.mass p.field (fun i => (p.mass_pos i).le) p.mass_sum

def law (p : RationalFieldLaw) : ProbabilityMeasure ℝ := ⟨p.measure,inferInstance⟩

def magneticValue (p : RationalFieldLaw) (R : ℝ → ℝ) : ℝ :=
  (finiteMagneticFunctional R p.mass p.field).toReal

lemma magneticValue_eq_of_law_eq (p q : RationalFieldLaw)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Set.Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (he : p.law=q.law) :
    p.magneticValue (measureR (ν : Measure ℝ) b)=q.magneticValue (measureR (ν : Measure ℝ) b) :=
  measureMagnetic_eq_of_field_law_eq ν a b hcompact hbound ha hb p.mass p.field q.mass q.field
    p.mass_pos q.mass_pos p.mass_sum q.mass_sum (congrArg ProbabilityMeasure.toMeasure he)

lemma integrable_id (p : RationalFieldLaw) : Integrable (fun x : ℝ => x) p.measure := by
  change Integrable (fun x : ℝ => x) (Measure.sum (fun i => ENNReal.ofReal (p.mass i) • Measure.dirac (p.field i)))
  rw [Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp)).smul_measure (by finiteness)

end RationalFieldLaw
end InvariantIsing

end

end OAI
