import Mathlib.Probability.Kernel.Disintegration.Unique

namespace OAI

/-! # Disintegration after adjoining an independent neutral coordinate -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree

variable {Z U V : Type*} [MeasurableSpace Z] [MeasurableSpace U] [MeasurableSpace V]

def exchangeLastCoordinates : (Z × U) × V ≃ᵐ (Z × V) × U where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  measurable_invFun := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

def independentCoordinateMeasure (ρ : Measure (Z × U)) (η : Measure V) :
    Measure ((Z × V) × U) := (ρ.prod η).map exchangeLastCoordinates

instance independentCoordinateMeasure_isFinite
    (ρ : Measure (Z × U)) [IsFiniteMeasure ρ] (η : Measure V) [IsFiniteMeasure η] :
    IsFiniteMeasure (independentCoordinateMeasure ρ η) := by
  unfold independentCoordinateMeasure
  infer_instance

lemma independentCoordinateMeasure_rectangle
    (ρ : Measure (Z × U)) [SFinite ρ] (η : Measure V) [SFinite η]
    {A : Set Z} {B : Set V} {C : Set U}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    independentCoordinateMeasure ρ η ((A ×ˢ B) ×ˢ C)=ρ (A ×ˢ C)*η B := by
  rw [independentCoordinateMeasure,
    Measure.map_apply exchangeLastCoordinates.measurable (hA.prod hB |>.prod hC)]
  have he : exchangeLastCoordinates ⁻¹' ((A ×ˢ B) ×ˢ C)=(A ×ˢ C) ×ˢ B := by
    ext z
    simp only [mem_preimage,mem_prod,exchangeLastCoordinates,
      MeasurableEquiv.coe_mk]
    tauto
  rw [he,Measure.prod_prod]

lemma independentCoordinateMeasure_fst
    (ρ : Measure (Z × U)) [IsFiniteMeasure ρ] (η : Measure V) [IsFiniteMeasure η] :
    (independentCoordinateMeasure ρ η).fst=ρ.fst.prod η := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.fst_apply (hA.prod hB)]
  rw [show Prod.fst ⁻¹' (A ×ˢ B)=((A ×ˢ B) ×ˢ (Set.univ : Set U)) by
    ext z; simp,
    independentCoordinateMeasure_rectangle ρ η hA hB MeasurableSet.univ,
    Measure.prod_prod,Measure.fst_apply hA]
  congr 2
  ext z
  simp

variable [StandardBorelSpace U] [Nonempty U]

theorem independentCoordinateMeasure_disintegrate
    (ρ : Measure (Z × U)) [IsFiniteMeasure ρ] (η : Measure V) [IsFiniteMeasure η] :
    independentCoordinateMeasure ρ η=
      (ρ.fst.prod η) ⊗ₘ (ρ.condKernel.comap Prod.fst measurable_fst) := by
  apply Measure.ext_prod₃'
  intro A B C hA hB hC
  rw [independentCoordinateMeasure_rectangle ρ η hA hB hC,
    Measure.compProd_apply_prod (hA.prod hB) hC]
  simp_rw [Kernel.comap_apply]
  rw [setLIntegral_prod (fun z : Z × V => ρ.condKernel z.1 C)
      (ρ.condKernel.measurable_coe hC |>.comp measurable_fst).aemeasurable,
    show (fun z : Z => ∫⁻ _ in B, ρ.condKernel z C ∂η)=
      (fun z => ρ.condKernel z C*η B) by
        funext z
        rw [lintegral_const,Measure.restrict_apply_univ],
    lintegral_mul_const'' _ (ρ.condKernel.measurable_coe hC).aemeasurable,
    Measure.setLIntegral_condKernel_eq_measure_prod hA hC]

theorem independentCoordinateMeasure_condKernel
    (ρ : Measure (Z × U)) [IsFiniteMeasure ρ] (η : Measure V) [IsFiniteMeasure η] :
    ∀ᵐ z ∂(independentCoordinateMeasure ρ η).fst,
      (independentCoordinateMeasure ρ η).condKernel z=ρ.condKernel z.1 := by
  have he := independentCoordinateMeasure_disintegrate ρ η
  rw [←independentCoordinateMeasure_fst ρ η] at he
  exact (eq_condKernel_of_measure_eq_compProd _ he).mono fun z hz => hz.symm

end DukePrimeDegree

end

end OAI
