import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisCurve

namespace OAI

/-! Exact reconstruction of the two source branches from their scalar
kernel-axis parameter in the actual crosscap chart. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

lemma axisCurve_coordinate (c : SurfaceCrosscapCoordinates f p) {x : M}
    (hx : x ∈ c.source.source) (hzero : c.source x 0 = 0) :
    c.axisCurve (c.source x 1) = x := by
  have he : crosscapAxis (c.source x 1) = c.source x := by
    rw [crosscapAxis_apply]
    ext i
    fin_cases i
    · exact hzero.symm
    · rfl
  change c.source.symm (crosscapAxis (c.source x 1)) = x
  rw [he,c.source.left_inv hx]

lemma axis_pair_coordinates (c : SurfaceCrosscapCoordinates f p) {x y : M}
    (hx : x ∈ c.source.source) (hy : y ∈ c.source.source)
    (h0x : c.source x 0 = 0) (h0y : c.source y 0 = 0)
    (hopp : c.source x 1 = -c.source y 1) :
    (x,y) = (c.axisCurve (c.source x 1),c.axisCurve (-c.source x 1)) := by
  apply Prod.ext
  · exact (c.axisCurve_coordinate hx h0x).symm
  · have he : -c.source x 1 = c.source y 1 := by linarith
    rw [he,c.axisCurve_coordinate hy h0y]

lemma axis_parameter_injective (c : SurfaceCrosscapCoordinates f p)
    {Γ : ℝ → M × M} {K : Set ℝ} (hΓ : K.InjOn Γ)
    (hsource : ∀ t ∈ K, (Γ t).1 ∈ c.source.source ∧ (Γ t).2 ∈ c.source.source)
    (haxis : ∀ t ∈ K, c.source (Γ t).1 0 = 0 ∧ c.source (Γ t).2 0 = 0 ∧
      c.source (Γ t).1 1 = -c.source (Γ t).2 1) :
    K.InjOn (fun t => c.source (Γ t).1 1) := by
  intro t ht u hu he
  apply hΓ ht hu
  have ht' := c.axis_pair_coordinates (hsource t ht).1 (hsource t ht).2
    (haxis t ht).1 (haxis t ht).2.1 (haxis t ht).2.2
  have hu' := c.axis_pair_coordinates (hsource u hu).1 (hsource u hu).2
    (haxis u hu).1 (haxis u hu).2.1 (haxis u hu).2.2
  change ((Γ t).1,(Γ t).2) = ((Γ u).1,(Γ u).2)
  dsimp only at he
  rw [ht',hu',he]

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
