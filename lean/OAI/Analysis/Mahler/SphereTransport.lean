import OAI.Analysis.Mahler.ComplexCoordinates
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace OAI

noncomputable section
open Set MeasureTheory Metric
open scoped Pointwise
namespace MahlerStokes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual restriction of a real linear isometry to the unit sphere. -/
def sphereIsometry (e : E ≃ₗᵢ[ℝ] F) : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 := by
  refine { toEquiv := ?_, continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact {
      toFun := fun x => ⟨e (x : E), by simpa only [mem_sphere, dist_zero_right, e.norm_map] using x.property⟩
      invFun := fun y => ⟨e.symm (y : F), by simpa only [mem_sphere, dist_zero_right, e.symm.norm_map] using y.property⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
  · exact (e.continuous.comp continuous_subtype_val).subtype_mk _
  · exact (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

lemma sphereIsometry_cone_preimage (e : E ≃ₗᵢ[ℝ] F) (s : Set (sphere (0 : F) 1)) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((sphereIsometry e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨r, hr, e z, ⟨sphereIsometry e z, hz, rfl⟩, (e.map_smul r z).symm⟩
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, he⟩
    refine ⟨r, hr, e.symm z, ⟨(sphereIsometry e).symm z, ?_, rfl⟩, ?_⟩
    · simpa using hz
    · apply e.injective
      simpa using he

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Surface area induced by ambient volume is transported without a factor
by a volume-preserving real linear isometry. -/
theorem measurePreserving_sphereIsometry (e : E ≃ₗᵢ[ℝ] F)
    (μ : Measure E) (ν : Measure F) (he : MeasurePreserving e μ ν) :
    MeasurePreserving (sphereIsometry e) μ.toSphere ν.toSphere := by
  refine ⟨(sphereIsometry e).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereIsometry e).measurable hs,
    Measure.toSphere_apply' _ ((sphereIsometry e).measurable hs),
    Measure.toSphere_apply' _ hs, sphereIsometry_cone_preimage]
  rw [e.toLinearEquiv.finrank_eq]
  congr 1
  exact he.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

/-- The explicit interleaved real/complex map preserves the actual unit sphere area. -/
theorem measurePreserving_interleavedSphere (n : ℕ) :
    MeasurePreserving (sphereIsometry (interleavedEuclidean n))
      (volume : Measure (EuclideanSpace ℝ (Fin (n*2)))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere :=
  measurePreserving_sphereIsometry _ _ _ (interleavedEuclidean n).measurePreserving

/-- No integrability hypothesis is needed for change of variables along the
measure-preserving measurable equivalence. -/
theorem integral_interleavedSphere (n : ℕ)
    (f : sphere (0 : EuclideanSpace ℂ (Fin n)) 1 → ℝ) :
    (∫ x, f (sphereIsometry (interleavedEuclidean n) x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n*2)))).toSphere) =
    ∫ z, f z ∂(volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere :=
  (measurePreserving_interleavedSphere n).integral_comp
    (sphereIsometry (interleavedEuclidean n)).measurableEmbedding f

end MahlerStokes

end

end OAI
