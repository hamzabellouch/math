import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def linearIsometrySphereHomeomorph (f : E ≃ₗᵢ[ℝ] F) :
    Metric.sphere (0:E) 1 ≃ₜ Metric.sphere (0:F) 1 :=
  f.toHomeomorph.sets (by ext x; simp)

@[simp] lemma linearIsometrySphereHomeomorph_coe (f : E ≃ₗᵢ[ℝ] F)
    (e : Metric.sphere (0:E) 1) :
    ((linearIsometrySphereHomeomorph f e : Metric.sphere (0:F) 1) : F) = f e := rfl

lemma linearIsometrySphere_cone_preimage (f : E ≃ₗᵢ[ℝ] F)
    (s : Set (Metric.sphere (0:F) 1)) :
    f ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0:ℝ) 1 • (Subtype.val '' ((linearIsometrySphereHomeomorph f) ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨t,ht,y,⟨e,he,rfl⟩,h⟩
    let d : Metric.sphere (0:E) 1 := ⟨f.symm e,by
      simp⟩
    refine ⟨t,ht,d,⟨d,?_,rfl⟩,?_⟩
    · change linearIsometrySphereHomeomorph f d ∈ s
      have hd : linearIsometrySphereHomeomorph f d = e := by ext; simp [d]
      rwa [hd]
    · apply f.injective
      simpa [d] using h
  · rintro ⟨t,ht,y,⟨e,he,rfl⟩,h⟩
    refine ⟨t,ht,f e,⟨linearIsometrySphereHomeomorph f e,he,rfl⟩,?_⟩
    rw [← h,map_smul]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/- The Haar-induced sphere measure is preserved by every linear isometry.
No surface-measure normalization or Jacobian identity is assumed. -/
theorem linearIsometrySphere_measurePreserving (f : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (linearIsometrySphereHomeomorph f)
      (volume : Measure E).toSphere (volume : Measure F).toSphere := by
  refine ⟨(linearIsometrySphereHomeomorph f).measurable,?_⟩
  ext s hs
  rw [Measure.map_apply (linearIsometrySphereHomeomorph f).measurable hs,
    Measure.toSphere_apply' _ ((linearIsometrySphereHomeomorph f).measurable hs),
    Measure.toSphere_apply' _ hs,← linearIsometrySphere_cone_preimage]
  have hp (t : Set F) : volume (f ⁻¹' t) = volume t := by
    calc
      volume (f ⁻¹' t) = (Measure.map f volume) t :=
        (f.toHomeomorph.measurableEmbedding.map_apply volume t).symm
      _ = volume t := congrArg (fun μ : Measure F => μ t) f.measurePreserving.map_eq
  rw [hp,f.toLinearEquiv.finrank_eq]

end AffineBernstein
end

end OAI
