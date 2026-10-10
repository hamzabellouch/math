import Mathlib

namespace OAI

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section
namespace CylinderCovering.OrthogonalFubini

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem volume_orthogonalSlices (K : Submodule ℝ E) {S : Set E}
    (hS : MeasurableSet S) :
    volume S = ∫⁻ y : K, volume {z : Kᗮ | (y : E) + (z : E) ∈ S} := by
  let f : K × Kᗮ → E := fun yz => (yz.1 : E) + (yz.2 : E)
  have hf : MeasurePreserving f := by
    have h := K.orthogonalDecomposition.symm.measurePreserving.comp
      (WithLp.volume_preserving_toLp K Kᗮ)
    simpa [f, Function.comp_def] using h
  have hm : MeasurableSet (f ⁻¹' S) := hS.preimage hf.measurable
  rw [← hf.measure_preimage hS.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply hm]
  rfl

theorem volume_orthogonalSlices_symm (K : Submodule ℝ E) {S : Set E}
    (hS : MeasurableSet S) :
    volume S = ∫⁻ y : Kᗮ, volume {z : K | (y : E) + (z : E) ∈ S} := by
  let f : K × Kᗮ → E := fun yz => (yz.1 : E) + (yz.2 : E)
  have hf : MeasurePreserving f := by
    have h := K.orthogonalDecomposition.symm.measurePreserving.comp
      (WithLp.volume_preserving_toLp K Kᗮ)
    simpa [f, Function.comp_def] using h
  have hm : MeasurableSet (f ⁻¹' S) := hS.preimage hf.measurable
  rw [← hf.measure_preimage hS.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply_symm hm]
  congr 1
  funext y
  congr 1
  ext z
  simp [f, add_comm]

def unitLineEquiv (u : E) (hu : ‖u‖ = 1) : ℝ ≃ₗᵢ[ℝ] (ℝ ∙ u) where
  __ := LinearEquiv.toSpanNonzeroSingleton ℝ E u (by
    intro h
    simp [h] at hu)
  norm_map' t := by simp [norm_smul, hu]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem unitLineEquiv_apply (u : E) (hu : ‖u‖ = 1) (t : ℝ) :
    ((unitLineEquiv u hu t : ℝ ∙ u) : E) = t • u := rfl

theorem volume_directionalSlices (u : E) (hu : ‖u‖ = 1) {S : Set E}
    (hS : MeasurableSet S) :
    volume S = ∫⁻ y : (ℝ ∙ u)ᗮ, volume {t : ℝ | (y : E) + t • u ∈ S} := by
  rw [volume_orthogonalSlices_symm (ℝ ∙ u) hS]
  apply lintegral_congr
  intro y
  have hm : MeasurableSet {z : ℝ ∙ u | (y : E) + (z : E) ∈ S} :=
    hS.preimage (measurable_const.add continuous_subtype_val.measurable)
  simpa using ((unitLineEquiv u hu).measurePreserving.measure_preimage
    hm.nullMeasurableSet).symm

end CylinderCovering.OrthogonalFubini

end

end OAI
