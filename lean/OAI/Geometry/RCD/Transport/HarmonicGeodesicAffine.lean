import OAI.Geometry.RCD.Transport.LocalHarmonicBoundedPlan
import OAI.Geometry.RCD.Coordinates.NormalizedSubplanData
import OAI.Geometry.RCD.Harmonic.AffinePathMeans

namespace OAI

/-! # Local harmonic constant-energy coordinates are affine on almost every optimal geodesic -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

include hn in
theorem harmonic_coordinate_affine_on_geodesics
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    {R : ℝ} (hR : 1 ≤ R)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (V : X → ℝ)
    {b : ℝ} (hb : 50*R < b)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict (ball p b)] V)
    (hH : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) u)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic u u x ≤ (L:ℝ)^2)
    (c : ℝ) (hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c)
    (hV : Continuous V) (hVc : HasCompactSupport V) :
    ∀ᵐ γ ∂π, ∀ t : Time, V (γ t)=(1-(t:ℝ))*V (γ 0)+(t:ℝ)*V (γ 1) := by
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded (π.map (fun γ => γ 0)) p hs₀)
    (finiteSecondMoment_of_bounded (π.map (fun γ => γ 1)) p hs₁) hopt.1 hopt.2.1
  apply affine_paths_of_normalized_means π V hV hVc
  intro κ hk hk0
  obtain ⟨hprob,hgeoκ,hoptκ,hcompκ,hsκ₀,hsκ₁⟩ := normalized_subplan_data π hgeo hopt hfin
    (hausdorff n X) hcomp p hs₀ hs₁ κ hk hk0
  let := hprob
  have hCκ : (κ univ)⁻¹*C ≠ ∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hk0) hC
  exact hX.local_harmonic_mean_on_bounded_plan hn p ((κ univ)⁻¹ • κ)
    hgeoκ hoptκ hCκ hcompκ hR hsκ₀ hsκ₁ u V hb hu hH L hL c hc

include hn in
theorem harmonic_coordinate_affine_on_geodesics_continuous
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    {R : ℝ} (hR : 1 ≤ R)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (V : X → ℝ)
    {b : ℝ} (hb : 50*R < b)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict (ball p b)] V)
    (hH : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) u)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic u u x ≤ (L:ℝ)^2)
    (c : ℝ) (hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c)
    (hV : Continuous V) :
    ∀ᵐ γ ∂π, ∀ t : Time, V (γ t)=(1-(t:ℝ))*V (γ 0)+(t:ℝ)*V (γ 1) := by
  have hb0 : 0 < b := by linarith
  let W := fun x => radialCutoff p b x*V x
  have hW : Continuous W := (radialCutoff_lipschitz p hb0).continuous.mul hV
  have hWc : HasCompactSupport W := (radialCutoff_hasCompactSupport p hb0).mul_right
  have huW : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict (ball p b)] W := by
    filter_upwards [hu,ae_restrict_mem measurableSet_ball] with x hx hxb
    rw [hx]
    dsimp only [W]
    have hxrad : dist p x ≤ b := by
      have hx' : dist x p < b := hxb
      simpa only [dist_comm] using hx'.le
    rw [radialCutoff_eq_one p hb0 hxrad,one_mul]
  have haff := hX.harmonic_coordinate_affine_on_geodesics hn p π hgeo hopt hC hcomp hR hs₀ hs₁
    u W hb huW hH L hL c hc hW hWc
  have hbounded := optimal_geodesic_plan_bounded (π.map (fun γ => γ 0))
    (π.map (fun γ => γ 1)) π hgeo hopt p (zero_le_one.trans hR) hs₀ hs₁
  filter_upwards [haff,hbounded] with γ hγ hbγ t
  have heq (s : Time) : W (γ s)=V (γ s) := by
    dsimp only [W]
    rw [radialCutoff_eq_one p hb0 (by
      rw [dist_comm]
      exact (hbγ.2 s).trans (by linarith)),one_mul]
  simpa only [heq] using hγ t

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
