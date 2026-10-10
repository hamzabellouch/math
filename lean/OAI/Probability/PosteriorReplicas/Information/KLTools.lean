import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma klDiv_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : X ≃ᵐ Y) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le _ _ e.measurable)
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self, Measure.map_id] using h

lemma klDiv_swap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure (X × Y)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map Prod.swap) (ν.map Prod.swap) = klDiv μ ν :=
  klDiv_map_equiv μ ν MeasurableEquiv.prodComm

lemma klDiv_prod_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] :
    klDiv (μ.prod ρ) (ν.prod ρ) = klDiv μ ν := by
  simpa only [Measure.compProd_const] using klDiv_compProd_left μ ν (Kernel.const X ρ)

lemma klDiv_prod_right {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν ρ : Measure Y) [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    klDiv (μ.prod ν) (μ.prod ρ) = klDiv ν ρ := by
  rw [← klDiv_swap, Measure.prod_swap, Measure.prod_swap, klDiv_prod_left]

lemma klDiv_prod_first_chain {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    (q : Measure (X × Y)) [IsProbabilityMeasure q]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν] :
    klDiv q (μ.prod ν) = klDiv q.fst μ + klDiv q (q.fst.prod ν) := by
  have h := klDiv_compProd_eq_add q.fst μ q.condKernel (Kernel.const X ν)
  simpa only [Measure.disintegrate q q.condKernel, Measure.compProd_const] using h

lemma klDiv_prod_decomposition {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (q : Measure (X × Y)) [IsProbabilityMeasure q]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν] :
    klDiv q (μ.prod ν) = klDiv q.fst μ + klDiv q.snd ν + klDiv q (q.fst.prod q.snd) := by
  rw [klDiv_prod_first_chain]
  have h := klDiv_prod_first_chain (q.map Prod.swap) ν q.fst
  rw [Measure.fst_map_swap] at h
  have h1 : klDiv (q.map Prod.swap) (ν.prod q.fst) = klDiv q (q.fst.prod ν) := by
    rw [← Measure.prod_swap, klDiv_swap]
  have h2 : klDiv (q.map Prod.swap) (q.snd.prod q.fst) = klDiv q (q.fst.prod q.snd) := by
    rw [← Measure.prod_swap, klDiv_swap]
  rw [h1, h2] at h
  rw [h, add_assoc]

section KernelKL
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountableOrCountablyGenerated X Y]
  (μ : Measure X) [IsFiniteMeasure μ] (κ η : Kernel X Y)
  [IsMarkovKernel κ] [IsMarkovKernel η]

lemma withDensity_kernel_rnDeriv (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (μ ⊗ₘ η).withDensity (fun z => κ.rnDeriv η z.1 z.2) = μ ⊗ₘ κ := by
  rw [← Measure.compProd_withDensity (Kernel.measurable_rnDeriv κ η)]
  apply Measure.compProd_congr
  filter_upwards [hac] with x hx
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv κ η)]
  rw [withDensity_congr_ae (Kernel.rnDeriv_eq_rnDeriv_measure), Measure.withDensity_rnDeriv_eq _ _ hx]

lemma rnDeriv_compProd_kernel (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] (fun z => κ.rnDeriv η z.1 z.2) := by
  conv_lhs => rw [← withDensity_kernel_rnDeriv μ κ η hac]
  exact Measure.rnDeriv_withDensity _ (Kernel.measurable_rnDeriv κ η)

lemma klDiv_compProd_kernel_integral (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  rw [klDiv_eq_lintegral_klFun_of_ac (Measure.AbsolutelyContinuous.compProd_right hac)]
  calc
    _ = ∫⁻ z, ENNReal.ofReal (klFun (κ.rnDeriv η z.1 z.2).toReal) ∂μ ⊗ₘ η := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_compProd_kernel μ κ η hac] with z hz
      rw [hz]
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (klFun (κ.rnDeriv η x y).toReal) ∂η x ∂μ := by
      rw [Measure.lintegral_compProd (by fun_prop)]
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hac] with x hx
      rw [klDiv_eq_lintegral_klFun_of_ac hx]
      apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := x)] with y hy
      rw [hy]

lemma measurable_kernel_klDiv : Measurable (fun x => klDiv (κ x) (η x)) := by
  classical
  have he : (fun x => klDiv (κ x) (η x)) = fun x =>
      if κ x ≪ η x then ∫⁻ y, ENNReal.ofReal (klFun (κ.rnDeriv η x y).toReal) ∂η x
      else ∞ := by
    funext x
    split_ifs with hx
    · rw [klDiv_eq_lintegral_klFun_of_ac hx]
      apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := x)] with y hy
      rw [hy]
    · exact klDiv_of_not_ac hx
  rw [he]
  apply Measurable.ite (Kernel.measurableSet_absolutelyContinuous κ η) _ measurable_const
  exact Measurable.lintegral_kernel_prod_right' (κ := η) (by
    exact ENNReal.measurable_ofReal.comp (continuous_klFun.measurable.comp
      (Kernel.measurable_rnDeriv κ η).ennreal_toReal))

lemma klDiv_compProd_kernel :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  by_cases hac : ∀ᵐ x ∂μ, κ x ≪ η x
  · exact klDiv_compProd_kernel_integral μ κ η hac
  · have hnot : ¬ μ ⊗ₘ κ ≪ μ ⊗ₘ η := fun h => hac h.kernel_of_compProd
    rw [klDiv_of_not_ac hnot]
    apply (eq_top_iff.mpr _).symm
    by_contra h
    have hfin : (∫⁻ x, klDiv (κ x) (η x) ∂μ) < ∞ := lt_of_not_ge h
    have ha := ae_lt_top (measurable_kernel_klDiv κ η) hfin.ne
    apply hac
    filter_upwards [ha] with x hx
    exact (klDiv_ne_top_iff.mp hx.ne).1

end KernelKL
end PosteriorReplicas
end

end OAI
