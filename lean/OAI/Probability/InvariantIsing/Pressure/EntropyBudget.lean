import OAI.Probability.InvariantIsing.Core.KernelRelativeEntropy
import OAI.Probability.InvariantIsing.Core.TiltedRelativeEntropy

namespace OAI

/-! Nonnegative entropy budgets for successive finite sampling steps. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped ENNReal

namespace InvariantIsing

lemma entropy_budget_of_real {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (D : X → ℝ) (hD : Integrable D μ) (hD0 : ∀ x, 0 ≤ D x)
    {c : ℝ} (hK : klDiv μ ν ≠ ⊤) (h : (klDiv μ ν).toReal + (∫ x, D x ∂μ) ≤ c) :
    klDiv μ ν + (∫⁻ x, ENNReal.ofReal (D x) ∂μ) ≤ ENNReal.ofReal c := by
  rw [← ofReal_integral_eq_lintegral_ofReal hD (Filter.Eventually.of_forall hD0),
    ← ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_add ENNReal.toReal_nonneg
      (integral_nonneg hD0)]
  exact ENNReal.ofReal_le_ofReal h

lemma entropy_budget_drop {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) (D : X → ℝ≥0∞)
    (h : ∀ x, kernelRelativeEntropy κ η x ≤ D x) :
    klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv μ ν + ∫⁻ x, D x ∂μ :=
  (klDiv_comp_le_integral μ ν κ η hac).trans (add_le_add_right (lintegral_mono h) _)

lemma entropy_budget_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → Y) (hf : Measurable f) (D : Y → ℝ≥0∞) (hD : Measurable D) :
    klDiv (μ.map f) (ν.map f) + (∫⁻ y, D y ∂μ.map f) ≤
      klDiv μ ν + ∫⁻ x, D (f x) ∂μ := by
  rw [lintegral_map hD hf]
  exact add_le_add_left (klDiv_map_le μ ν hf) _

lemma tilted_pair_entropy_budget_ennreal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ)
    (hFG : Integrable (fun x => F x - G x) (μ.tilted (fun x => b * G x)))
    (hGF : ∀ x, G x ≤ F x) :
    klDiv (μ.tilted (fun x => b * G x)) (μ.tilted (fun x => b * F x)) +
      (∫⁻ x, ENNReal.ofReal (F x - G x) ∂μ.tilted (fun x => b * G x)) ≤
      ENNReal.ofReal (logMean b μ F - logMean b μ G) :=
  entropy_budget_of_real _ _ _ hFG (fun x => sub_nonneg.mpr (hGF x))
    (tilted_pair_entropy_identity μ F G hb hF hG hFG).1
    (tilted_pair_entropy_budget μ F G hb hb1 hF hG hFG)

end InvariantIsing

end

end OAI
