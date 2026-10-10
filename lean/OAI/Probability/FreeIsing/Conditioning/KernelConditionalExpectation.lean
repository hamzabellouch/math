import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω]
    {ν : Measure W} [IsFiniteMeasure ν] {κ : Kernel W Ω} [IsMarkovKernel κ]

theorem condExp_compProd_fst {f : W × Ω → ℝ} (hf : Integrable f (ν ⊗ₘ κ)) :
    (ν ⊗ₘ κ)[f | (inferInstance : MeasurableSpace W).comap Prod.fst] =ᵐ[ν ⊗ₘ κ]
      fun z => ∫ x, f (z.1, x) ∂κ z.1 := by
  have hmap : (ν ⊗ₘ κ).map (fun z : W × Ω => (z.1, z.2)) =
      (ν ⊗ₘ κ).map Prod.fst ⊗ₘ κ := by
    change (ν ⊗ₘ κ).map id = (ν ⊗ₘ κ).fst ⊗ₘ κ
    rw [Measure.map_id, Measure.fst_compProd]
  have hk := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := ν ⊗ₘ κ) (κ := κ) measurable_fst measurable_snd hmap
  have hc := condExp_prod_ae_eq_integral_condDistrib'
    (μ := ν ⊗ₘ κ) (X := Prod.fst) (Y := Prod.snd) (f := f)
    measurable_fst measurable_snd.aemeasurable
    (by
      change Integrable f ((ν ⊗ₘ κ).map id)
      simpa only [Measure.map_id] using hf)
  filter_upwards [hc, ae_of_ae_map measurable_fst.aemeasurable hk] with z hcz hkz
  simpa only [Prod.mk.eta, hkz] using hcz

end Problem367

end

end OAI
