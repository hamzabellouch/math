import OAI.Geometry.CylinderCovering.Barycentric.EnclosureDefinitions
import OAI.Geometry.CylinderCovering.Barycentric.CanonicalEnclosure

namespace OAI

noncomputable section
namespace RadialCoordinates.BarycentricSector

theorem enclosureStatement : EnclosureStatement where
  triangles := fun _ _ _ _ hlr ha hb =>
    ⟨isCompact_signedSector hlr ha hb, signedSector_eq_two_triangles hlr ha hb,
      positive_negative_inter hlr ha hb⟩
  exactArea := fun _ _ _ _ => signedSector_area
  nondegenerate := fun _ _ _ => vertices_affineIndependent
  uniformPerimeters := fun _ _ _ _ _ => collar_perimeters_le
  actualIntercepts := fun _ _ _ _ _ _ _ _ => frozen_intercept_mem_cthickening
  geometricError := fun _ _ _ _ _ hl hlr hr hk hM hMM =>
    ⟨neighborhood_isCompact hlr hk hM, neighborhood_area_error hl hlr hr hk hM hMM⟩
  weightedFinite := fun _ hN _ _ hk M hM hMM S hS W hW0 hW1 =>
    equal_cell_intercepted_area_bound hN hk M hM hMM S hS W hW0 hW1
  canonicalCompact := intercepts_isCompact
  canonicalFinite := fun _ hN _ hk => canonical_equal_cell_area_bound hN hk

end RadialCoordinates.BarycentricSector

end

end OAI
