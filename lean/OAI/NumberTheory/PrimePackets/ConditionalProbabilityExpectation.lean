import OAI.NumberTheory.PrimePackets.ObservationSigmaAlgebra

namespace OAI

/-! # Identification with genuine conditional expectation -/

noncomputable section
open MeasureTheory Set

namespace PrimeDegreePackets

variable {Y α β : Type*} [MeasurableSpace Y] [Fintype β]

omit [Fintype β] in
lemma setIntegral_observationConditionalProbability
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) (a : α) (b : β) :
    (∫ y in {y | Q y = b}, observationConditionalProbability μ P Q a y ∂μ) =
      μ.real {y | (Q y,P y) = (b,a)} := by
  have heq : (fun y => observationConditionalProbability μ P Q a y) =ᵐ[μ.restrict {y | Q y = b}]
      (fun _ => μ.real {y | (Q y,P y) = (b,a)} / μ.real {y | Q y = b}) := by
    filter_upwards [ae_restrict_mem (hQ b)] with y hy
    simp only [observationConditionalProbability, hy]
  rw [integral_congr_ae heq, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  by_cases hb : μ.real {y | Q y = b} = 0
  · have hz : μ.real {y | (Q y,P y) = (b,a)} = 0 := by
      apply le_antisymm _ measureReal_nonneg
      have hsub : {y | (Q y,P y) = (b,a)} ⊆ {y | Q y = b} :=
        fun y hy => congrArg Prod.fst hy
      calc
        _ ≤ μ.real {y | Q y = b} :=
          measureReal_mono hsub (measure_ne_top _ _)
        _ = 0 := hb
    rw [hb,hz]
    simp only [zero_div,mul_zero]
  · exact mul_div_cancel₀ _ hb

theorem observationConditionalProbability_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) (a : α) :
    observationConditionalProbability μ P Q a =ᵐ[μ]
      μ[({y | P y = a}.indicator (fun _ => (1 : ℝ))) | observationSigma Q] := by
  apply observation_values_ae_eq_condExp μ Q hQ _ ((integrable_const (1 : ℝ)).indicator (hP a))
    (fun b => μ.real {y | (Q y,P y) = (b,a)} / μ.real {y | Q y = b})
  intro b
  change (∫ y in {y | Q y = b}, observationConditionalProbability μ P Q a y ∂μ) = _
  rw [setIntegral_observationConditionalProbability μ P Q hQ a b,
    integral_indicator (hP a), integral_const]
  simp only [measureReal_restrict_apply_univ, measureReal_restrict_apply (hP a), smul_eq_mul, mul_one]
  apply congrArg μ.real
  ext y
  simp only [Prod.mk.injEq, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

end PrimeDegreePackets

end

end OAI
