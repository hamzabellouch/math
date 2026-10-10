import OAI.Geometry.CylinderCovering.Beams.NeighborhoodSimilarityDefinitions
import OAI.Geometry.CylinderCovering.Beams.NeighborhoodCovers
import OAI.Geometry.CylinderCovering.Beams.RectangleSimilarity
import OAI.Geometry.CylinderCovering.Ruled.Similarity

namespace OAI

noncomputable section
open Set
namespace ShortenedBeam
open CylinderCovering

theorem regularTetrahedron_beam_similarity {K : Set Space}
    (hK : IsRegularTetrahedron K) :
    ∃ t : Space, ∃ r : ℝ, ∃ L : Space ≃ₗᵢ[ℝ] Space,
      0 < r ∧ K = Similarity.map t r L '' tetrahedron := by
  rcases hK with ⟨v, hv, edge, hedge, hdist, rfl⟩
  obtain ⟨L, t, h⟩ := RegularSimplexSimilarity.regular_simplex_similarity
    vertices v vertices_affineIndependent hv
    (show 0 < 2*Real.sqrt 2 by positivity) hedge
    (fun _ _ hij => vertices_edge_length hij) hdist
  refine ⟨t, edge/(2*Real.sqrt 2), L, by positivity, ?_⟩
  rw [tetrahedron_eq_vertices]
  exact h

private lemma similarity_base_image (C : RuledApproximation.Cylinder)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    Subtype.val '' (C.similarity t hr L).base =
      Similarity.transportedBase (Subtype.val '' C.base) C.axis t r L := by
  exact RuledApproximation.similarityPlaneMap_image C.axis C.unit_axis t hr L C.base

private lemma similarity_base_compact (C : RuledApproximation.Cylinder)
    (hC : IsCompact C.base) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) : IsCompact (C.similarity t hr L).base := by
  exact hC.image
    (RuledApproximation.similarityPlaneMap C.axis C.unit_axis t hr L).toAffineMap.continuous_of_finiteDimensional

private lemma similarity_rectangular (C : RuledApproximation.Cylinder)
    (hC : BeamStrip.HasRectangularBase C) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) : BeamStrip.HasRectangularBase (C.similarity t hr L) := by
  unfold BeamStrip.HasRectangularBase
  rw [similarity_base_image]
  exact hC.transportedBase C.axis t hr L

theorem neighborhoodFamilies_similarity {a : ℝ} {N : ℕ}
    {Cm Cp : Fin N → RuledApproximation.Cylinder}
    (hfamilies : NeighborhoodFamilies a N Cm Cp)
    (t : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    TransportedNeighborhoodFamilies a N t r L
      (fun i => (Cm i).similarity t hr L) (fun i => (Cp i).similarity t hr L) := by
  obtain ⟨hlocal, hminus, hplus⟩ := hfamilies
  refine ⟨?_, RuledApproximation.similarity_cover Cm _ hminus t hr L,
    RuledApproximation.similarity_cover Cp _ hplus t hr L⟩
  intro i
  obtain ⟨haxisM, haxisP, hbaseM, hbaseP, hcompactM, hcompactP⟩ := hlocal i
  refine ⟨?_, ?_, ?_, ?_, similarity_base_compact _ hcompactM t hr L,
    similarity_base_compact _ hcompactP t hr L⟩
  · exact congrArg L haxisM
  · exact congrArg L haxisP
  · rw [similarity_base_image, hbaseM, haxisM]
  · rw [similarity_base_image, hbaseP, haxisP]

theorem regularNeighborhoodStatement : RegularNeighborhoodStatement := by
  intro K hK
  obtain ⟨t, r, L, hr, hsim⟩ := regularTetrahedron_beam_similarity hK
  obtain ⟨a, ha, ha1, N, hN, Cm, Cp, n, D,
    hfamilies, hD, hstrip, hcover, hcost⟩ := neighborhoodStrictStatement
  have hr0 : r ≠ 0 := ne_of_gt hr
  let Cm' := fun i => (Cm i).similarity t hr0 L
  let Cp' := fun i => (Cp i).similarity t hr0 L
  let D' := fun j => (D j).similarity t hr0 L
  refine ⟨a, ha, ha1, t, r, L, hr, hsim, N, hN, Cm', Cp', n, D',
    neighborhoodFamilies_similarity hfamilies t hr0 L, ?_,
    RuledApproximation.similarity_cover D _ hstrip t hr0 L, ?_, ?_⟩
  · intro j
    exact ⟨similarity_rectangular _ (hD j).hasRectangularBase t hr0 L,
      similarity_base_compact _ (hD j).isCompact t hr0 L⟩
  · rw [hsim]
    have h := image_mono hcover (f := Similarity.map t r L)
    simpa only [image_union, RuledApproximation.similarity_familySet, Cm', Cp', D'] using h
  · change RuledApproximation.familyArea (fun i => (Cm i).similarity t hr0 L) +
      RuledApproximation.familyArea (fun i => (Cp i).similarity t hr0 L) +
      RuledApproximation.familyArea (fun j => (D j).similarity t hr0 L) < _
    rw [RuledApproximation.similarity_familyArea, RuledApproximation.similarity_familyArea,
      RuledApproximation.similarity_familyArea, hsim]
    change r^2 * RuledApproximation.familyArea Cm + r^2 * RuledApproximation.familyArea Cp +
      r^2 * RuledApproximation.familyArea D <
        Similarity.minimumArea (Similarity.map t r L '' tetrahedron)/2
    rw [Similarity.minimumArea_map _ _ hr0 L]
    change _ < r^2 * minimumShadowArea tetrahedron/2
    nlinarith only [mul_lt_mul_of_pos_left hcost (sq_pos_of_pos hr)]

end ShortenedBeam

end

end OAI
