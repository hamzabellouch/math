import OAI.Geometry.RCD.Transport.LocalHarmonicGeodesic

namespace OAI

/-! # One full-measure geodesic set for the entire harmonic coordinate family -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

include hn in
theorem harmonic_family_affine_on_geodesics
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    {R : ℝ} (hR : 1 ≤ R)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    {b : ℝ} (hb : 50*R < b)
    (hu : ∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i)
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun x => v x i)
    (hH : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) (u i))
    (L : Fin n → ℝ≥0) (hL : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic (u i) (u i) x ≤ (L i:ℝ)^2)
    (c : Fin n → ℝ) (hc : ∀ i, localGamma (hausdorff n X) hX.quadratic (u i) (u i)
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c i)
    (hv : ContinuousOn v (ball p b)) :
    ∀ᵐ γ ∂π, ∀ t : Time, v (γ t)=(1-(t:ℝ)) • v (γ 0)+(t:ℝ) • v (γ 1) := by
  have hi (i : Fin n) : ∀ᵐ γ ∂π, ∀ t : Time,
      v (γ t) i=(1-(t:ℝ))*v (γ 0) i+(t:ℝ)*v (γ 1) i :=
    hX.local_harmonic_coordinate_affine_on_geodesics hn p π hgeo hopt hC hcomp hR hs₀ hs₁
      (u i) (fun x => v x i) hb (hu i) (hH i) (L i) (hL i) (c i) (hc i) (by fun_prop)
  filter_upwards [ae_all_iff.mpr hi] with γ hγ t
  ext i
  simpa only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] using hγ i t

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
