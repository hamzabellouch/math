import OAI.Geometry.ProjectionVolume.Basic
import Mathlib.MeasureTheory.Group.Action

namespace OAI

open Set MeasureTheory
open scoped Pointwise

namespace Paper092

theorem projectionVolume_vadd {n : ℕ} (K : Set (Euclidean n)) (v u : Euclidean n) :
    projectionVolume (v +ᵥ K) u = projectionVolume K u := by
  unfold projectionVolume
  let p := (normalHyperplane u).orthogonalProjectionOnto
  have himage : p '' (v +ᵥ K) = p v +ᵥ (p '' K) := by
    change p '' ((fun x => v + x) '' K) = (fun y => p v + y) '' (p '' K)
    simp only [image_image, map_add]
  rw [himage, measure_vadd]

theorem brightness_vadd {n : ℕ} (K : Set (Euclidean n)) (v u : Euclidean n) :
    brightness (v +ᵥ K) u = brightness K u := by
  simp only [brightness, projectionVolume_vadd]

theorem projectionBody_vadd {n : ℕ} (K : Set (Euclidean n)) (v : Euclidean n) :
    projectionBody (v +ᵥ K) = projectionBody K := by
  ext y
  simp only [projectionBody, mem_ofPred_eq, brightness_vadd]

theorem normalizedProjectionVolume_vadd {n : ℕ} (K : Set (Euclidean n))
    (v : Euclidean n) :
    normalizedProjectionVolume (v +ᵥ K) = normalizedProjectionVolume K := by
  simp only [normalizedProjectionVolume, projectionBody_vadd, measure_vadd]

end Paper092

end OAI
