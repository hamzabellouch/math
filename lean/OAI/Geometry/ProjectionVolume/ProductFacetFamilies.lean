import OAI.Geometry.ProjectionVolume.ProductFacets
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Paper092

theorem eq_exposedFace_of_isExposed {n : ℕ} {K F : Set (Euclidean n)}
    (hF : IsExposed ℝ K F) (hne : F.Nonempty) : ∃ u, F = exposedFace K u := by
  obtain ⟨l, hl⟩ := hF hne
  let u := (InnerProductSpace.toDual ℝ (Euclidean n)).symm l
  refine ⟨u, ?_⟩
  have hu : innerSL ℝ u = l := by
    ext x
    change ⟪(InnerProductSpace.toDual ℝ (Euclidean n)).symm l, x⟫ = l x
    exact InnerProductSpace.toDual_symm_apply
  change F = (innerSL ℝ u).toExposed K
  rw [hu]
  exact hl

theorem product_facet_families {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A : Set (Euclidean r)) (B : Set (Euclidean s)) (hA : IsCompact A) (hB : IsCompact B)
    (hiA : (interior A).Nonempty) (hiB : (interior B).Nonempty)
    (F : Set (Euclidean (r + s))) (hF : IsExposed ℝ (cartesianBody A B) F)
    (hne : F.Nonempty) (hdim : Module.finrank ℝ (vectorSpan ℝ F) = r + s - 1) :
    (∃ u : Euclidean r, u ≠ 0 ∧
      Module.finrank ℝ (vectorSpan ℝ (exposedFace A u)) = r - 1 ∧
      F = cartesianBody (exposedFace A u) B) ∨
    (∃ v : Euclidean s, v ≠ 0 ∧
      Module.finrank ℝ (vectorSpan ℝ (exposedFace B v)) = s - 1 ∧
      F = cartesianBody A (exposedFace B v)) := by
  obtain ⟨w, rfl⟩ := eq_exposedFace_of_isExposed hF hne
  rcases exposedFace_product_facet_classification hr hs A B hA hB hiA hiB w hdim with h | h
  · exact Or.inl ⟨(splitEuclideanProduct r s w).1, h.1, h.2.2⟩
  · exact Or.inr ⟨(splitEuclideanProduct r s w).2, h.2.1, h.2.2⟩

end Paper092

end

end OAI
