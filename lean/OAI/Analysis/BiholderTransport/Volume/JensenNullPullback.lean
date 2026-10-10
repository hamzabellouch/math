import Mathlib
import OAI.Analysis.BiholderTransport.Volume.ContactJacobianMeasure

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_nonsingular_map_avoids_null {Y : E → E} {D : E → E →L[ℝ] E}
    {N : Set E} (hN : μ N=0) :
    ∀ᵐ z ∂μ,HasFDerivAt Y (D z) z → (D z).det≠0 → Y z∉N := by
  let Z := {z | HasFDerivAt Y (D z) z ∧ (D z).det≠0 ∧ Y z∈N}
  have hZ : μ Z=0 := measure_eq_zero_of_nonsingular_null_image μ
    (fun z hz => hz.1.hasFDerivWithinAt) (fun z hz => hz.2.1)
    (measure_mono_null (by rintro _ ⟨z,hz,rfl⟩; exact hz.2.2) hN)
  have H : ∀ᵐ z ∂μ,z∉Z := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hZ
  filter_upwards [H] with z hz hd hdet hmem
  exact hz ⟨hd,hdet,hmem⟩
end WeakMTWTransport

end

end OAI
