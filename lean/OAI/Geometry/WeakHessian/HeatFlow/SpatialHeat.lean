import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SetDensities
import OAI.Geometry.WeakHessian.HeatFlow.CompactHeatPairing
import OAI.Geometry.WeakHessian.Curvature.Doubling

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile80
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma exists_lipschitz_of_ball_averages [IsLocallyFiniteMeasure m] [IsUnifLocDoublingMeasure m]
    (g : Lp ℝ 2 m) {C : ℝ≥0}
    (h : ∀ x y : X, ∀ r : ℝ,0 < r →
      |(⨍ z in Metric.closedBall x r,g z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m)| ≤
        (C:ℝ)*(2*r+dist x y)) :
    ∃ g' : X → ℝ,LipschitzWith C g' ∧ g' =ᵐ[m] g := by
  let S : Set X := {x | Tendsto (fun r : ℝ => ⨍ z in Metric.closedBall x r,g z ∂m) (𝓝[>] 0) (𝓝 (g x))}
  have hS : ∀ᵐ x ∂m,x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average m ((Lp.memLp g).locallyIntegrable (by norm_num)) 1] with x hx
    apply hx (fun _ : ℝ => x) id tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using hr.le
  have hLip : LipschitzOnWith C (g : X → ℝ) S := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq]
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have H := le_of_tendsto_of_tendsto (hx.sub hy |>.abs)
      (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hr).add tendsto_const_nhds))
      (show ∀ᶠ r in 𝓝[>] (0:ℝ), |(⨍ z in Metric.closedBall x r,g z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m)| ≤ (C:ℝ)*(2*r+dist x y) from
        by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact h x y r hr)
    simpa only [mul_zero,zero_add] using H
  obtain ⟨g',hg',heq⟩ := hLip.extend_real
  exact ⟨g',hg',hS.mono fun x hx => (heq hx).symm⟩

variable [ProperSpace X] [SigmaFinite m]

lemma RCD.cheegerHeat_lipschitzVersion {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) {D : ℝ} (hfB : ∀ x,|f x| ≤ D)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ g : X → ℝ,LipschitzWith (L*⟨Real.exp (-K*t),(Real.exp_pos _).le⟩) g ∧
      g =ᵐ[m] cheegerHeat h t (hf2.toLp f) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let : IsUnifLocDoublingMeasure m := hrcd.1.uniform_local_doubling hN hfull hfin
  apply exists_lipschitz_of_ball_averages
  intro x y r hr
  have hm (x : X) : m (Metric.closedBall x r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
  have hp (x : X) : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let u (x : X) := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hn (x : X) : ∀ᵐ z ∂m,0 ≤ u x z := setDensity_nonneg _ _ _
  have hmass (x : X) : ∫ z,u x z ∂m = 1 := setDensity_mass _ _ _ (hp x)
  have hb (x : X) : ∀ᵐ z ∂m,|u x z| ≤ (m (Metric.closedBall x r)).toReal⁻¹ := setDensity_bounded _ _ _
  have hs (x : X) : ∀ᵐ z ∂m,r < dist z x → u x z = 0 := setDensity_supported _ _ _ x (Subset.refl _)
  have H := hrcd.cheegerHeat_pairing_balls hN hfull hfin h hf hf2 hfB (u x) (u y)
    (hn x) (hn y) (hmass x) (hmass y) (by positivity) (by positivity) (hb x) (hb y) x y hr.le hr.le (hs x) (hs y) ht
  have heq (x : X) : ⟪cheegerHeat h t (hf2.toLp f),u x⟫_ℝ =
      (⨍ z in Metric.closedBall x r,cheegerHeat h t (hf2.toLp f) z ∂m) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial]
    rw [setDensity_pairing,setAverage_eq,measureReal_def,smul_eq_mul]
  rw [heq x,heq y] at H
  change _ ≤ (L:ℝ)*Real.exp (-K*t)*(2*r+dist x y)
  simpa only [two_mul] using H
end WeakHessian

end
end InlinedFile80

end OAI
