import OAI.Probability.InvariantIsing.Core.KernelRelativeEntropy

namespace OAI

/-! Entropy of two independent continuations from a common state. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace InvariantIsing

lemma klDiv_prod_eq_add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ ν : Measure X) (ρ σ : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] (hac : ρ ≪ σ) :
    klDiv (μ.prod ρ) (ν.prod σ) = klDiv μ ν + klDiv ρ σ := by
  have he := klDiv_compProd_integral μ ν (Kernel.const X ρ) (Kernel.const X σ)
    (fun _ => hac)
  have hconst (x : X) : kernelRelativeEntropy (Kernel.const X ρ) (Kernel.const X σ) x =
      klDiv ρ σ := kernelRelativeEntropy_eq _ _ x hac
  simpa only [Measure.compProd_const, hconst, lintegral_const, measure_univ, mul_one] using he

lemma klDiv_prod_self {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountableOrCountablyGenerated X X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    klDiv (μ.prod μ) (ν.prod ν) = 2 * klDiv μ ν := by
  rw [klDiv_prod_eq_add μ ν μ ν hac, two_mul]

lemma entropy_budget_double {k d c : ℝ≥0∞} (h : k + d ≤ c) : k + 2 * d ≤ 2 * c := by
  calc
    k + 2 * d ≤ 2 * k + 2 * d := by
      exact add_le_add_left (show k ≤ 2 * k by simp only [two_mul]; exact le_self_add) _
    _ = 2 * (k + d) := (mul_add _ _ _).symm
    _ ≤ 2 * c := mul_le_mul_right h 2

end InvariantIsing

end

end OAI
