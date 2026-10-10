import OAI.Geometry.RCD.Transport.HarmonicFamilyGeodesicAffine
import OAI.Geometry.RCD.Transport.BoundedEndpointPlan

namespace OAI

/-! # Affine harmonic-coordinate geodesics with endpoints near prescribed points -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

include hn in
theorem exists_nearby_affine_geodesic {R : ℝ} (hR : 1 ≤ R)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    {b : ℝ} (hb : 50*R < b)
    (hu : ∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i)
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun x => v x i)
    (hH : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) (u i))
    (L : Fin n → ℝ≥0) (hL : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic (u i) (u i) x ≤ (L i:ℝ)^2)
    (c : Fin n → ℝ) (hc : ∀ i, localGamma (hausdorff n X) hX.quadratic (u i) (u i)
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c i)
    (hv : ContinuousOn v (ball p b))
    {x y : X} {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R/2)
    (hx : dist x p ≤ R/2) (hy : dist y p ≤ R/2) :
    ∃ γ : C(Time,X), IsGeodesic γ ∧ dist (γ 0) x < ρ ∧ dist (γ 1) y < ρ ∧
      (∀ t : Time, dist (γ t) p ≤ 3*R) ∧
      ∀ t : Time, v (γ t)=(1-(t:ℝ)) • v (γ 0)+(t:ℝ) • v (γ 1) := by
  have hsub (z : X) (hz : dist z p ≤ R/2) : ball z ρ ⊆ closedBall p R := by
    intro w hw
    have hdist : dist w z < ρ := hw
    change dist w p ≤ R
    linarith [dist_triangle w z p]
  obtain ⟨π,hπ,C,hC,hgeo,hopt,hcomp,hends,hs₀,hs₁⟩ := hX.bounded_endpoint_plan hn p
    (show 0<R by linarith) measurableSet_ball measurableSet_ball
    (hX.fullSupport x ρ hρ).ne' (hX.fullSupport y ρ hρ).ne' (hsub x hx) (hsub y hy)
  let := hπ
  have haff := hX.harmonic_family_affine_on_geodesics hn p π hgeo hopt hC hcomp hR hs₀ hs₁
    u v hb hu hH L hL c hc hv
  obtain ⟨γ,hγ,hend,hlin⟩ := (hgeo.and (hends.and haff)).exists
  exact ⟨γ,hγ,hend.1,hend.2.1,hend.2.2,hlin⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
