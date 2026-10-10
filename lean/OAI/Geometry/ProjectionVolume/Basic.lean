import OAI.Geometry.ProjectionVolume.Model

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem normalHyperplane_volume_is_canonical {n : ℕ} (u : Euclidean n) :
    (volume : Measure (normalHyperplane u)) =
      (stdOrthonormalBasis ℝ (normalHyperplane u)).toBasis.addHaar := rfl

theorem normalHyperplane_finrank {n : ℕ} (u : Euclidean n) (hu : u ≠ 0) :
    Module.finrank ℝ (normalHyperplane u) = n - 1 := by
  have h := (Submodule.span ℝ ({u} : Set (Euclidean n))).finrank_add_finrank_orthogonal
  simp only [finrank_span_singleton hu, finrank_euclideanSpace_fin] at h
  change Module.finrank ℝ ((Submodule.span ℝ ({u} : Set (Euclidean n)))ᗮ) = n - 1
  omega

end Paper092

end

end OAI
