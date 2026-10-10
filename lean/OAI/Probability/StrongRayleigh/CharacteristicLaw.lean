import Mathlib

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem336AdditiveD139.CharacteristicLaw

variable {Ω : Type u_1} {E : Type u_2} {m mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure E} [IsFiniteMeasure ν]
    {Z : Ω → E}

theorem map_restrict_eq_smul_of_characteristic
    (hZ : Measurable Z) (A : Set Ω)
    (hchar : ∀ t : E,
      (∫ ω in A, Complex.exp ((inner ℝ (Z ω) t : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) * charFun ν t) :
    Measure.map Z (μ.restrict A) = μ A • ν := by
  let : IsFiniteMeasure (μ A • ν) := ν.smul_finite (measure_ne_top μ A)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, integral_map hZ.aemeasurable (by fun_prop), hchar t]
  simp only [charFun_apply, integral_smul_measure, Complex.real_smul]

theorem map_eq_of_event_characteristic
    (hZ : Measurable Z) [IsProbabilityMeasure μ]
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ t : E,
      (∫ ω in A, Complex.exp ((inner ℝ (Z ω) t : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) * charFun ν t) :
    Measure.map Z μ = ν := by
  simpa using map_restrict_eq_smul_of_characteristic hZ Set.univ
    (hchar Set.univ MeasurableSet.univ)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] [IsFiniteMeasure μ] [IsFiniteMeasure ν] in

theorem independent_of_restricted_law
    [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hm : m ≤ mΩ)
    (hlaw : Measure.map Z μ = ν)
    (hrestrict : ∀ A : Set Ω, MeasurableSet[m] A →
      Measure.map Z (μ.restrict A) = μ A • ν) :
    Indep m (MeasurableSpace.comap Z inferInstance) μ := by
  rw [indep_iff_forall_indepSet]
  intro A B hA hB
  obtain ⟨C, hC, rfl⟩ := hB
  apply (indepSet_iff_measure_inter_eq_mul (hm A hA) (hZ hC) μ).2
  have hr := congrArg (fun ρ : Measure E => ρ C) (hrestrict A hA)
  have hu := congrArg (fun ρ : Measure E => ρ C) hlaw
  rw [Measure.map_apply hZ hC, Measure.restrict_apply (hZ hC),
    Measure.smul_apply, smul_eq_mul] at hr
  rw [Measure.map_apply hZ hC] at hu
  simpa only [Set.inter_comm, hu] using hr

theorem law_and_independent_of_event_characteristic
    [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hm : m ≤ mΩ)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ t : E,
      (∫ ω in A, Complex.exp ((inner ℝ (Z ω) t : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) * charFun ν t) :
    Measure.map Z μ = ν ∧ Indep m (MeasurableSpace.comap Z inferInstance) μ := by
  have hlaw := map_eq_of_event_characteristic hZ hchar
  refine ⟨hlaw, independent_of_restricted_law hZ hm hlaw ?_⟩
  intro A hA
  exact map_restrict_eq_smul_of_characteristic hZ A (hchar A hA)

theorem indepFun_of_event_characteristic
    [IsProbabilityMeasure μ] (hZ : Measurable Z)
    (hm : m ≤ mΩ)
    (hchar : ∀ A : Set Ω, MeasurableSet[m] A → ∀ t : E,
      (∫ ω in A, Complex.exp ((inner ℝ (Z ω) t : ℂ) * Complex.I) ∂μ) =
        ((μ A).toReal : ℂ) * charFun ν t)
    {Y : Type u_3} [MeasurableSpace Y] {X : Ω → Y} (hX : Measurable[m] X) :
    IndepFun X Z μ := by
  have h := (law_and_independent_of_event_characteristic hZ hm hchar).2
  exact indep_of_indep_of_le_left h hX.comap_le

end Problem336AdditiveD139.CharacteristicLaw

end

end OAI
