import OAI.Geometry.CylinderCovering.Footprints.CertificatesDefinitions
import OAI.Geometry.CylinderCovering.Footprints.Shapes

namespace OAI

namespace CylinderCovering.Footprints

theorem localFootprintCertificates : LocalFootprintCertificates where
  intercept_identity := quadraticIntercept_transverse
  arbitrary_absolute := fun _ _ _ _ _ _ _ _ _ _ => quadratic_mem_absolute
  midpoint_absolute := fun _ _ _ _ _ _ _ _ _ => quadratic_mem_absolute_midpoint
  midpoint_affine := fun _ _ _ _ _ _ _ _ _ => quadratic_mem_affine_midpoint
  endpoint_affine := fun _ _ _ _ _ _ _ => quadratic_mem_endpoint
  absolute_area := fun _ _ _ _ _ => realVolume_absoluteFootprint
  affine_area := fun _ _ _ _ _ => realVolume_affineFootprint
  absolute_compact := isCompact_absoluteFootprint
  affine_compact := isCompact_affineFootprint
  affine_convex := convex_affineFootprint
  absolute_not_convex := fun _ _ _ _ _ => not_convex_absoluteFootprint
  endpoint_identity := endpointFootprint_eq_affine
  triangle_hull := fun _ _ _ _ => affineFootprint_half_eq_convexHull
  triangle_independent := fun _ _ _ _ => affineFootprint_half_vertices_independent
  trapezoid_hull := fun _ _ _ _ _ => affineFootprint_eq_convexHull_trapezoid
  trapezoid_distinct := fun _ _ _ _ _ => trapezoidVertices_injective
  trapezoid_sides := trapezoid_vertical_sides
  midpoint_inclusion := fun _ _ _ _ => midpoint_affine_subset_absolute
  midpoint_finite_difference := midpoint_area_difference

end CylinderCovering.Footprints

end OAI
