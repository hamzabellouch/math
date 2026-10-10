import OAI.NumberTheory.DukePrimeDegree.Entropy.SelfConditionalKernelMap

namespace OAI

/-! # Moving a conditional kernel by an invariant coordinate change -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

def transportKernel (e : Y ≃ᵐ Y) (κ : Kernel Y Y) : Kernel Y Y :=
  (κ.comap e.symm e.symm.measurable).map e

lemma transportKernel_apply (e : Y ≃ᵐ Y) (κ : Kernel Y Y) (x : Y) :
    transportKernel e κ x=(κ (e.symm x)).map e := by
  rw [transportKernel,Kernel.map_apply _ e.measurable,Kernel.comap_apply]

instance transportKernel_markov (e : Y ≃ᵐ Y) (κ : Kernel Y Y) [IsMarkovKernel κ] :
    IsMarkovKernel (transportKernel e κ) := by
  unfold transportKernel
  exact Kernel.IsMarkovKernel.map _ e.measurable

theorem transportKernel_stationary (e : Y ≃ᵐ Y)
    (μ : Measure Y) [IsFiniteMeasure μ] (he : μ.map e=μ)
    (κ : Kernel Y Y) [IsMarkovKernel κ] (hstat : μ.bind κ=μ) :
    μ.bind (transportKernel e κ)=μ := by
  have heinv : μ.map e.symm=μ := by
    have H := congrArg (fun ν : Measure Y => ν.map e.symm) he
    rw [Measure.map_map e.symm.measurable e.measurable] at H
    simpa only [Function.comp_def,e.symm_apply_apply,Measure.map_id'] using H.symm
  apply bind_eq_of_real_integrals
  intro A hA
  have hEA : MeasurableSet (e ⁻¹' A) := hA.preimage e.measurable
  calc
    _ = ∫ x, (κ (e.symm x)).real (e ⁻¹' A) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => congrArg ENNReal.toReal (by
        rw [transportKernel_apply,Measure.map_apply e.measurable hA])
    _ = ∫ x, (κ x).real (e ⁻¹' A) ∂μ := by
      change (∫ x, (κ (e.symm x) (e ⁻¹' A)).toReal ∂μ)=_
      rw [←integral_map e.symm.measurable.aemeasurable
        (κ.measurable_coe hEA).ennreal_toReal.aestronglyMeasurable,heinv]
      rfl
    _ = (μ.bind κ).real (e ⁻¹' A) := (bind_kernel_real κ μ _ hEA).symm
    _ = μ.real A := by
      rw [hstat]
      exact congrArg ENNReal.toReal ((Measure.map_apply e.measurable hA).symm.trans
        (congrArg (fun ν : Measure Y => ν A) he))

theorem transportKernel_self_constant [StandardBorelSpace Y]
    (e : Y ≃ᵐ Y) (μ : Measure Y) (he : μ.map e=μ)
    (κ : Kernel Y Y) [IsMarkovKernel κ] (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂transportKernel e κ x,
      transportKernel e κ y=transportKernel e κ x := by
  have H := selfConstant_kernel_map μ κ hstat hself e e.measurable
    (transportKernel e κ) (ae_of_all _ fun x => by
      rw [transportKernel_apply,e.symm_apply_apply])
  rwa [he] at H

end DukePrimeDegree

end

end OAI
