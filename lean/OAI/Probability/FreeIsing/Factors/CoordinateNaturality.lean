import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem condExp_comp_measurableEquiv
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace β) (hm : m ≤ mβ)
    {f : β → ℝ} (hf : Integrable f ν) :
    μ[f ∘ e | m.comap e] =ᵐ[μ] (ν[f | m]) ∘ e := by
  let : MeasurableSpace β := mβ
  have hsource : m.comap e ≤ mα :=
    (MeasurableSpace.comap_mono hm).trans e.measurable.comap_le
  have hcompint : Integrable ((ν[f | m]) ∘ e) μ :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr integrable_condExp
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hsource
    ((he.integrable_comp_emb e.measurableEmbedding).mpr hf)
    (fun _ _ _ => hcompint.integrableOn)
  · intro A hA _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    simp only [Function.comp_apply]
    rw [he.setIntegral_preimage_emb e.measurableEmbedding,
      he.setIntegral_preimage_emb e.measurableEmbedding,
      setIntegral_condExp hm hf hB]
  · exact (stronglyMeasurable_condExp.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

def coordinateRelabelEquiv {ι A : Type*} [MeasurableSpace A] (e : ι ≃ ι) :
    (ι → A) ≃ᵐ (ι → A) where
  toFun x i := x (e.symm i)
  invFun x i := x (e i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  measurable_toFun := Measurable.of_eval (fun _ => measurable_pi_apply _)
  measurable_invFun := Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem comap_coordinateRelabel_cylinderEvents
    {ι A : Type*} [MeasurableSpace A] (e : ι ≃ ι) (D : Set ι) :
    (cylinderEvents (X := fun _ : ι => A) D).comap (coordinateRelabelEquiv e) =
      cylinderEvents (e ⁻¹' D) := by
  simp only [cylinderEvents, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun hi => ?_
    exact le_iSup_of_le (e.symm i) (le_iSup_of_le (by simpa using hi) le_rfl)
  · refine iSup_le fun i => iSup_le fun hi => ?_
    refine le_iSup_of_le (e i) (le_iSup_of_le hi ?_)
    simp only [Function.comp_def, coordinateRelabelEquiv, MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk, Equiv.symm_apply_apply]
    exact le_rfl

theorem condExp_coordinate_relabel
    {ι A : Type*} [MeasurableSpace A]
    (μ : Measure (ι → A)) [IsFiniteMeasure μ]
    (e : ι ≃ ι) (he : MeasurePreserving (coordinateRelabelEquiv e) μ μ)
    (D : Set ι) {f : (ι → A) → ℝ} (hf : Integrable f μ) :
    μ[f ∘ coordinateRelabelEquiv e | cylinderEvents (e ⁻¹' D)] =ᵐ[μ]
      (μ[f | cylinderEvents D]) ∘ coordinateRelabelEquiv e := by
  rw [← comap_coordinateRelabel_cylinderEvents e D]
  exact condExp_comp_measurableEquiv μ μ (coordinateRelabelEquiv e) he
    (cylinderEvents D) cylinderEvents_le_pi hf

theorem condExp_coordinate_invariant
    {ι A : Type*} [MeasurableSpace A]
    (μ : Measure (ι → A)) [IsFiniteMeasure μ]
    (e : ι ≃ ι) (he : MeasurePreserving (coordinateRelabelEquiv e) μ μ)
    (D : Set ι) (hD : e ⁻¹' D = D)
    {f : (ι → A) → ℝ} (hf : Integrable f μ)
    (hfi : f ∘ coordinateRelabelEquiv e =ᵐ[μ] f) :
    (μ[f | cylinderEvents D]) ∘ coordinateRelabelEquiv e =ᵐ[μ]
      μ[f | cylinderEvents D] := by
  have h := condExp_coordinate_relabel μ e he D hf
  rw [hD] at h
  exact h.symm.trans (condExp_congr_ae hfi)

end Problem367

end

end OAI
