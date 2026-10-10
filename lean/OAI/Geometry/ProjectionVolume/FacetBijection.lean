import OAI.Geometry.ProjectionVolume.FacetExhaustiveness
import OAI.Geometry.ProjectionVolume.FacetUniqueness
import OAI.Geometry.ProjectionVolume.ProductFacetFamilies

namespace OAI

universe uι

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem face_eq_exposedFace (i : ι) (hne : (P.face i).Nonempty) :
    P.face i = exposedFace P.body (P.normal i) := by
  ext x
  constructor
  · rintro ⟨hx, hxi⟩
    refine ⟨hx, ?_⟩
    intro y hy
    change ⟪P.normal i, y⟫ ≤ ⟪P.normal i, x⟫
    rw [hxi]
    exact hy i
  · intro hx
    obtain ⟨y, hy⟩ := hne
    refine ⟨hx.1, le_antisymm (hx.1 i) ?_⟩
    have h := hx.2 y hy.1
    change ⟪P.normal i, y⟫ ≤ ⟪P.normal i, x⟫ at h
    rwa [hy.2] at h

theorem face_isExposed (i : ι) : IsExposed ℝ P.body (P.face i) := by
  intro hne
  refine ⟨innerSL ℝ (P.normal i), ?_⟩
  exact P.face_eq_exposedFace i hne

theorem exposed_facet_eq_unique_face (hd : 0 < d) (F : Set (Euclidean d))
    (hF : IsExposed ℝ P.body F) (hne : F.Nonempty)
    (hdim : Module.finrank ℝ (vectorSpan ℝ F) = d - 1) :
    ∃! i, F = P.face i := by
  obtain ⟨u, rfl⟩ := eq_exposedFace_of_isExposed hF hne
  have hu : u ≠ 0 := by
    intro hzero
    rw [hzero, exposedFace_zero,
      vectorSpan_finrank_of_interior_nonempty P.body P.body_interior_nonempty] at hdim
    omega
  obtain ⟨i, hi⟩ := P.exposedFace_eq_face hu hdim
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply P.face_index_unique_of_finrank j i
  · rwa [← hj]
  · rwa [← hj]
  · exact hj.symm.trans hi

theorem finite_exposed_facets (hd : 0 < d) :
    {F : Set (Euclidean d) | IsExposed ℝ P.body F ∧ F.Nonempty ∧
      Module.finrank ℝ (vectorSpan ℝ F) = d - 1}.Finite := by
  apply (Set.finite_range P.face).subset
  rintro F ⟨hF, hne, hdim⟩
  obtain ⟨i, hi, _⟩ := P.exposed_facet_eq_unique_face hd F hF hne hdim
  exact ⟨i, hi.symm⟩

end Paper092.HPolytope

end

end OAI
