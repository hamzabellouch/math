import OAI.Geometry.RCD.Transport.HarmonicGeodesicAffine
import Mathlib.Topology.TietzeExtension

namespace OAI

/-! # Pointwise affine geodesics for genuinely local continuous harmonic coordinates -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

include hn in
theorem local_harmonic_coordinate_affine_on_geodesics
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
    (hV : ContinuousOn V (ball p b)) :
    ∀ᵐ γ ∂π, ∀ t : Time, V (γ t)=(1-(t:ℝ))*V (γ 0)+(t:ℝ)*V (γ 1) := by
  let r := (50*R+b)/2
  have hrb : r<b := by dsimp only [r]; linarith
  have hr50 : 50*R<r := by dsimp only [r]; linarith
  have hclosed : closedBall p r ⊆ ball p b := closedBall_subset_ball hrb
  let f : C(closedBall p r,ℝ) := ⟨fun x => V x,continuousOn_iff_continuous_domRestrict.mp (hV.mono hclosed)⟩
  obtain ⟨W,hW⟩ := f.exists_restrict_eq isClosed_closedBall
  have heq (x : X) (hx : x ∈ closedBall p r) : W x=V x := by
    exact congrArg (fun g : C(closedBall p r,ℝ) => g ⟨x,hx⟩) hW
  have hsub : ball p r ⊆ ball p b := ball_subset_ball hrb.le
  have huW : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict (ball p r)] W := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hu,ae_restrict_mem measurableSet_ball]
      with x hx hxr
    exact hx.trans (heq x (ball_subset_closedBall hxr)).symm
  have haff := hX.harmonic_coordinate_affine_on_geodesics_continuous hn p π hgeo hopt hC hcomp
    hR hs₀ hs₁ u W hr50 huW (hH.mono _ _ hsub) L
    (ae_restrict_of_ae_restrict_of_subset hsub hL) c
    (ae_restrict_of_ae_restrict_of_subset hsub hc) W.continuous
  have hbounded := optimal_geodesic_plan_bounded (π.map (fun γ => γ 0))
    (π.map (fun γ => γ 1)) π hgeo hopt p (zero_le_one.trans hR) hs₀ hs₁
  filter_upwards [haff,hbounded] with γ hγ hbγ t
  have he (s : Time) : W (γ s)=V (γ s) := heq _ (by
    rw [mem_closedBall]
    exact (hbγ.2 s).trans (by linarith))
  simpa only [he] using hγ t

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
