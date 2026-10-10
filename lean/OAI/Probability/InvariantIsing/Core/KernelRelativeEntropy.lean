import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

namespace OAI

/-! The conditional entropy identity needed for the finite Gaussian
sampling path. Its nonnegative integral form also covers zero variances. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace InvariantIsing

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountableOrCountablyGenerated X Y]

/-- A measurable version of conditional relative entropy, for dominated kernels. -/
def kernelRelativeEntropy (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (x : X) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (klFun ((κ.rnDeriv η x y).toReal)) ∂η x

lemma measurable_kernelRelativeEntropy (κ η : Kernel X Y)
    [IsMarkovKernel κ] [IsMarkovKernel η] : Measurable (kernelRelativeEntropy κ η) := by
  unfold kernelRelativeEntropy
  apply Measurable.lintegral_kernel_prod_right' (κ := η)
    (f := fun p : X × Y => ENNReal.ofReal (klFun ((κ.rnDeriv η p.1 p.2).toReal)))
  exact ENNReal.measurable_ofReal.comp
    (continuous_klFun.measurable.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal)

lemma kernelRelativeEntropy_eq (κ η : Kernel X Y)
    [IsMarkovKernel κ] [IsMarkovKernel η] (x : X) (hac : κ x ≪ η x) :
    kernelRelativeEntropy κ η x = klDiv (κ x) (η x) := by
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  apply lintegral_congr_ae
  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := x)] with y hy
  rw [hy]

lemma klDiv_compProd_same_left (μ : Measure X) [IsProbabilityMeasure μ]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, kernelRelativeEntropy κ η x ∂μ := by
  have hac' : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right (Filter.Eventually.of_forall hac)
  rw [klDiv_eq_lintegral_klFun_of_ac hac']
  calc
    _ = ∫⁻ p, ENNReal.ofReal (klFun ((κ.rnDeriv η p.1 p.2).toReal)) ∂(μ ⊗ₘ η) := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_measure_compProd_right μ κ η] with p hp
      rw [hp]
    _ = _ := Measure.lintegral_compProd (by
      exact ENNReal.measurable_ofReal.comp
        (continuous_klFun.measurable.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal))

lemma klDiv_compProd_integral (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + ∫⁻ x, kernelRelativeEntropy κ η x ∂μ := by
  rw [klDiv_compProd_eq_add, klDiv_compProd_same_left μ κ η hac]

lemma klDiv_comp_le_integral (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) :
    klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv μ ν + ∫⁻ x, kernelRelativeEntropy κ η x ∂μ := by
  have he := klDiv_map_le (μ ⊗ₘ κ) (ν ⊗ₘ η) measurable_snd
  change klDiv (μ ⊗ₘ κ).snd (ν ⊗ₘ η).snd ≤ _ at he
  rw [Measure.snd_compProd, Measure.snd_compProd,
    klDiv_compProd_integral μ ν κ η hac] at he
  exact he

end InvariantIsing

end

end OAI
