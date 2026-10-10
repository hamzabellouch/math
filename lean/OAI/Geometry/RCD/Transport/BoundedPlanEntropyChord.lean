import OAI.Geometry.RCD.Transport.SegmentEntropyConvexity

namespace OAI

/-! # Uniform curvature error on each bounded transport subinterval -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem bounded_plan_entropy_chord (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R) (s t r : Time) :
    boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ (timeSegment s t r))) ≤
      (1-(r:ℝ))*boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ s))+
      (r:ℝ)*boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ t))+
      (|K|/2)*(2*R)^2*(r:ℝ)*(1-(r:ℝ))*|(s:ℝ)-(t:ℝ)|^2 := by
  have h := hX.compressed_plan_segment_entropy hn p hR π hg hp hcomp hs₀ hs₁ s t r
  have hW : (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))).toReal ≤ (2*R)^2 := by
    simpa only [dist_self,zero_add] using wassersteinSq_ball_bound p p hR hs₀ hs₁
  let W := (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))).toReal
  have hKW : -K*W ≤ |K| * (2*R)^2 :=
    (mul_le_mul_of_nonneg_right (neg_le_abs K) ENNReal.toReal_nonneg).trans
      (mul_le_mul_of_nonneg_left hW (abs_nonneg K))
  have hr : 0 ≤ (r:ℝ)*(1-(r:ℝ))*|(s:ℝ)-(t:ℝ)|^2/2 := by
    exact div_nonneg (mul_nonneg (mul_nonneg r.property.1 (sub_nonneg.mpr r.property.2))
      (sq_nonneg _)) (by norm_num)
  have hcost := mul_le_mul_of_nonneg_left hKW hr
  dsimp only [W] at hcost
  nlinarith only [h,hcost]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
