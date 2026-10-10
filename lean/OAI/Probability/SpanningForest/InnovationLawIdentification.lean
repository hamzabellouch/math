import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem336.InnovationLawIdentification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [mE : MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem map_restrict_eq_smul_of_charFun
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure E) [IsFiniteMeasure ν]
    (X : Ω → E) (A : Set Ω)
    (h : ∀ t : E, charFun ((P.restrict A).map X) t =
      ((P A).toReal : ℂ) * charFun ν t) :
    (P.restrict A).map X = P A • ν := by
  have : IsFiniteMeasure (P A • ν) := ν.smul_finite (measure_ne_top P A)
  apply Measure.ext_of_charFun
  funext t
  rw [h t]
  simp only [charFun_apply, integral_smul_measure, RCLike.real_smul_eq_coe_mul]
  rfl

theorem hasLaw_and_indepFun_of_restricted_charFun
    {F : Type*} [MeasurableSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [IsFiniteMeasure ν]
    (X : Ω → E) (Y : Ω → F) (hX : Measurable X)
    (h : ∀ B : Set F, MeasurableSet B → ∀ t : E,
      charFun ((P.restrict (Y ⁻¹' B)).map X) t =
        ((P (Y ⁻¹' B)).toReal : ℂ) * charFun ν t) :
    HasLaw X ν P ∧ IndepFun X Y P := by
  have hrestricted (B : Set F) (hB : MeasurableSet B) :
      (P.restrict (Y ⁻¹' B)).map X = P (Y ⁻¹' B) • ν :=
    map_restrict_eq_smul_of_charFun P ν X (Y ⁻¹' B) (h B hB)
  have hlaw : P.map X = ν := by
    simpa using hrestricted Set.univ MeasurableSet.univ
  refine ⟨⟨hX.aemeasurable, hlaw⟩,
    indepFun_iff_measure_inter_preimage_eq_mul.mpr ?_⟩
  intro s t hs ht
  have heq := congrArg (fun ρ : Measure E => ρ s) (hrestricted t ht)
  rw [Measure.map_apply hX hs, Measure.restrict_apply (hs.preimage hX),
    Measure.smul_apply] at heq
  have hmargin : P (X ⁻¹' s) = ν s := by
    rw [← hlaw, Measure.map_apply hX hs]
  rw [heq, hmargin]
  exact mul_comm _ _

theorem hasLaw_and_indep_of_restricted_charFun
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [IsFiniteMeasure ν]
    (X : Ω → E) (hX : Measurable X) (past : MeasurableSpace Ω)
    (hpast : past ≤ mΩ)
    (h : ∀ A : Set Ω, MeasurableSet[past] A → ∀ t : E,
      charFun (@Measure.map Ω E mΩ mE X (P.restrict A)) t =
        ((P A).toReal : ℂ) * charFun ν t) :
    HasLaw X ν P ∧ Indep (MeasurableSpace.comap X mE) past P := by
  let : MeasurableSpace Ω := mΩ
  have hrestricted (A : Set Ω) (hA : MeasurableSet[past] A) :
      (P.restrict A).map X = P A • ν :=
    map_restrict_eq_smul_of_charFun P ν X A (h A hA)
  have hlaw : P.map X = ν := by
    simpa using hrestricted Set.univ MeasurableSet.univ
  refine ⟨⟨hX.aemeasurable, hlaw⟩, (indep_iff_forall_indepSet P).mpr ?_⟩
  intro s A hs hA
  rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨B, hB, rfl⟩
  apply (indepSet_iff_measure_inter_eq_mul (hB.preimage hX) (hpast A hA) P).mpr
  have heq := congrArg (fun ρ : Measure E => ρ B) (hrestricted A hA)
  rw [Measure.map_apply hX hB, Measure.restrict_apply (hB.preimage hX),
    Measure.smul_apply] at heq
  have hmargin : P (X ⁻¹' B) = ν B := by
    rw [← hlaw, Measure.map_apply hX hB]
  rw [heq, hmargin]
  exact mul_comm _ _

theorem hasLaw_and_indep_of_restricted_integral
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [IsFiniteMeasure ν]
    (X : Ω → E) (hX : Measurable X) (past : MeasurableSpace Ω)
    (hpast : past ≤ mΩ)
    (h : ∀ A : Set Ω, MeasurableSet[past] A → ∀ t : E,
      (∫ ω in A, Complex.exp ((inner ℝ (X ω) t : ℝ) * Complex.I) ∂P) =
        ((P A).toReal : ℂ) * charFun ν t) :
    HasLaw X ν P ∧ Indep (MeasurableSpace.comap X mE) past P := by
  let : MeasurableSpace Ω := mΩ
  apply hasLaw_and_indep_of_restricted_charFun P ν X hX past hpast
  intro A hA t
  rw [charFun_apply, integral_map hX.aemeasurable (by fun_prop)]
  exact h A hA t

end Problem336.InnovationLawIdentification

end

end OAI
