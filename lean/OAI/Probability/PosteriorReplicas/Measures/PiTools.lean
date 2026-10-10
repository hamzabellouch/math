import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma lintegral_pi_cons {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    {n : ℕ} {f : (Fin (n+1) → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => μ) =
      ∫⁻ p, ∫⁻ v : Fin n → E, f (Fin.cons p v) ∂Measure.pi (fun _ => μ) ∂μ := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) 0).symm
  have he (z : E × (Fin n → E)) : e z = Fin.cons z.1 z.2 := by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  rw [← hm.lintegral_comp hf]
  change (∫⁻ z, f (e z) ∂μ.prod (Measure.pi (fun _ : Fin n => μ))) = _
  have hfe : Measurable (fun z => f (e z)) := hf.comp e.measurable
  rw [lintegral_prod _ hfe.aemeasurable]
  simp_rw [he]

lemma ae_pi_cons {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    {n : ℕ} {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => μ), P v) ↔
      ∀ᵐ p ∂μ, ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => μ), P (Fin.cons p v) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) 0).symm
  have he (z : E × (Fin n → E)) : e z = Fin.cons z.1 z.2 := by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  rw [← hm.map_eq, MeasurableEmbedding.ae_map_iff e.measurableEmbedding]
  have hPe : MeasurableSet {z | P (e z)} := hP.preimage e.measurable
  rw [Measure.ae_prod_iff_ae_ae hPe]
  simp_rw [he]

end PosteriorReplicas
end

end OAI
