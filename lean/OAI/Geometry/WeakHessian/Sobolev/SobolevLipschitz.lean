import Mathlib
import OAI.Geometry.WeakHessian.Transport.DensityMeasure
import OAI.Geometry.WeakHessian.Geodesics.SquareControl
import OAI.Geometry.WeakHessian.LocalBounds.SetDensities

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile137
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocallyL2.locallyIntegrable (hfin : FiniteOnBoundedSets m) {f : X → ℝ}
    (hf : LocallyL2 m f) : LocallyIntegrable f m := by
  intro x
  let : IsFiniteMeasure (m.restrict (Metric.ball x 1)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,(hf x 1 zero_lt_one).integrable (by norm_num)⟩

lemma exists_lipschitz_of_local_ball_averages [IsLocallyFiniteMeasure m] [IsUnifLocDoublingMeasure m]
    {g : X → ℝ} (hg : LocallyIntegrable g m) {C : ℝ≥0}
    (h : ∀ x y : X, ∀ r : ℝ,0 < r →
      |(⨍ z in Metric.closedBall x r,g z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m)| ≤
        (C:ℝ)*(2*r+dist x y)) :
    ∃ g' : X → ℝ,LipschitzWith C g' ∧ g' =ᵐ[m] g := by
  let S : Set X := {x | Tendsto (fun r : ℝ => ⨍ z in Metric.closedBall x r,g z ∂m) (𝓝[>] 0) (𝓝 (g x))}
  have hS : ∀ᵐ x ∂m,x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average m hg 1] with x hx
    apply hx (fun _ : ℝ => x) id tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using hr.le
  have hLip : LipschitzOnWith C g S := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq]
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have H := le_of_tendsto_of_tendsto (hx.sub hy |>.abs)
      (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hr).add tendsto_const_nhds))
      (show ∀ᶠ r in 𝓝[>] (0:ℝ), |(⨍ z in Metric.closedBall x r,g z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m)| ≤ (C:ℝ)*(2*r+dist x y) from by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact h x y r hr)
    simpa only [mul_zero,zero_add] using H
  obtain ⟨g',hg',heq⟩ := hLip.extend_real
  exact ⟨g',hg',hS.mono fun x hx => (heq hx).symm⟩

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma IsLocalWeakUpperGradient.geodesic_endpoint_lipschitz {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {C : ℝ≥0} (hbD : ∀ᵐ x ∂m,D x ≤ C) {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ) :
    ∀ᵐ γ ∂π,|f (γ timeOne)-f (γ timeZero)| ≤ (C:ℝ)*dist (γ timeZero) (γ timeOne) := by
  filter_upwards [hD.ae_endpoint_le hf hπ hb,hπ.ae_ae_eval_of_ae hbD,hgeo] with γ hγ hDγ hg
  have H : (∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal (D (evalReal γ t))*metricSpeed γ t) ≤
      ENNReal.ofReal ((C:ℝ)*dist (γ timeZero) (γ timeOne)) := by
    calc
      _ ≤ ∫⁻ _t in Icc (0:ℝ) 1,ENNReal.ofReal (C:ℝ)*ENNReal.ofReal (dist (γ timeZero) (γ timeOne)) := by
        apply lintegral_mono_ae
        filter_upwards [hDγ,hg.ae_metricSpeed_le] with t ht hs
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal ht) hs
      _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,
        ENNReal.ofReal_one,mul_one,ENNReal.ofReal_mul C.coe_nonneg]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.coe_nonneg dist_nonneg)).mp (hγ.trans H)

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_setDensity (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) (f : X → ℝ) :
    (∫ x,f x ∂densityMeasure m (setDensity S hS hfin)) = ⨍ x in S,f x ∂m := by
  rw [integral_densityMeasure m _ (setDensity_nonneg S hS hfin),setAverage_eq,measureReal_def,smul_eq_mul,
    ← integral_const_mul,← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [setDensity_coe S hS hfin] with x hx
  rw [hx]
  by_cases hxs : x ∈ S <;> simp [hxs]

end WeakHessian

end
end InlinedFile137

end OAI
