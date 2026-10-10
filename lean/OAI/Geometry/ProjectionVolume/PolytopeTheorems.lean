import OAI.Geometry.ProjectionVolume.PolytopeCauchy

namespace OAI

universe uι

open scoped RealInnerProductSpace

namespace Paper092

theorem polytope_brightness {d : ℕ} (_hd : 2 ≤ d) {ι : Type uι} [Fintype ι]
    (P : HPolytope d ι) (u : Euclidean d) :
    brightness P.body u = (1 / 2 : ℝ) * ∑ i, P.faceArea i * |⟪P.normal i, u⟫| := by
  simpa only [real_inner_comm, div_eq_mul_inv, one_mul, mul_comm] using P.brightness_eq_sum u

theorem polytope_projectionBody {d : ℕ} (_hd : 2 ≤ d) {ι : Type uι} [Fintype ι]
    (P : HPolytope d ι) : projectionBody P.body = P.facetZonotope :=
  P.projectionBody_eq_facetZonotope

end Paper092

end OAI
