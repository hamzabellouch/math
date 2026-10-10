import OAI.Geometry.RCD.Transport.StrongEntropyMeasure

namespace OAI

/-! # Strong entropy convexity on every bounded compressed optimal plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_plan_entropy_convexity (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R) (t : Time) :
    boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ t)) ≤
      (1-(t:ℝ))*boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ 0))+
      (t:ℝ)*boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ 1))-
      (K/2)*(t:ℝ)*(1-(t:ℝ))*
        (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))).toReal := by
  let : CompleteSpace X := hX.complete
  let : Nonempty X := nonempty_of_isProbabilityMeasure (π.map (fun γ => γ 0))
  have hfin := coupling_transportCost_ne_top hp.1 hp.2.1 p
    (integrable_dist_sq_of_ae_bounded _ p hs₀) (integrable_dist_sq_of_ae_bounded _ p hs₁)
  have he (s t : Time) :
      (wassersteinSq (π.map (fun γ => γ s)) (π.map (fun γ => γ t))).toReal=
        |(s:ℝ)-(t:ℝ)|^2*
          (wassersteinSq (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))).toReal := by
    rw [wassersteinSq_eq_cost (geodesic_plan_optimal_marginals π hg hp hfin s t),
      geodesic_plan_cost π hg,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),wassersteinSq_eq_cost hp]
  have hsupport : ∀ᵐ x ∂π.map (fun γ => γ t), dist x p ≤ 3*R := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable
      (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hg hp p hR hs₀ hs₁).mono fun γ hγ => hγ.2 t
  apply hX.bounded_entropy_geodesic_measure hn p _ _ _ (hcomp 0) (hcomp 1) (hcomp t)
    hs₀ hs₁ hsupport t.property.1 t.property.2
  · rw [he]
    simp only [show ((0 : Time) : ℝ) = 0 from rfl,sub_zero,
      abs_of_nonneg t.property.1]
  · rw [he]
    simp only [show ((1 : Time) : ℝ) = 1 from rfl,
      abs_of_nonpos (sub_nonpos.mpr t.property.2),neg_sub]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
