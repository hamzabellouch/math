import OAI.MeasureTheory.Falconer.Angular.SphereModel
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-!
# Rotation invariance of the actual sphere measure

The sphere measure used by the energy is defined from Euclidean volume.
Its invariance follows directly by transporting its defining truncated
cones through a linear isometry.
-/

namespace Falconer
open Set MeasureTheory
open scoped Pointwise

def sphereMap {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) : Sphere d :=
  ⟨e w, by simpa only [Metric.mem_sphere,dist_zero_right,e.norm_map] using w.property⟩

theorem continuous_sphereMap {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) :
    Continuous (sphereMap e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _

noncomputable def sphereHomeomorph {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) : Sphere d ≃ₜ Sphere d where
  toFun := sphereMap e
  invFun := sphereMap e.symm
  left_inv := by intro w; apply Subtype.ext; simp [sphereMap]
  right_inv := by intro w; apply Subtype.ext; simp [sphereMap]
  continuous_toFun := continuous_sphereMap e
  continuous_invFun := continuous_sphereMap e.symm

theorem sphereMap_cone_preimage {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (s : Set (Sphere d)) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((sphereMap e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨r,hr,e w,⟨sphereMap e w,hw,rfl⟩,by simp⟩
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,heq⟩
    refine ⟨r,hr,e.symm w,⟨sphereMap e.symm w,?_,rfl⟩,?_⟩
    · change sphereMap e (sphereMap e.symm w) ∈ s
      convert hw using 1
      apply Subtype.ext
      simp [sphereMap]
    · have hh := congrArg e.symm heq
      simpa using hh

theorem sphereMap_measurePreserving {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) :
    MeasurePreserving (sphereMap e) (sphereMeasure d) (sphereMeasure d) := by
  have hm := (continuous_sphereMap e).measurable
  refine ⟨hm,Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs]
  unfold sphereMeasure
  rw [Measure.toSphere_apply' _ (hm hs),Measure.toSphere_apply' _ hs,sphereMap_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

theorem sphere_integral_rotation {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (f : Sphere d → ℂ) :
    (∫ w, f (sphereMap e w) ∂sphereMeasure d) = ∫ w, f w ∂sphereMeasure d :=
  (sphereMap_measurePreserving e).integral_comp (sphereHomeomorph e).measurableEmbedding f

end Falconer

end OAI
