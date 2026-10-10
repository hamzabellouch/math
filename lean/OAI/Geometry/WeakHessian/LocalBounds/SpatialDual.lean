import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SetDensities
import OAI.Geometry.WeakHessian.HeatFlow.DualHeatPairing
import OAI.Geometry.WeakHessian.Curvature.Doubling

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile81
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FullSupport.openPosMeasure (h : FullSupport m) : Measure.IsOpenPosMeasure m :=
  ⟨fun U ho hn => (h U ho hn).ne'⟩

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma continuous_le_of_ae_le (hfull : FullSupport m) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ᵐ x ∂m,f x ≤ g x) : ∀ x,f x ≤ g x := by
  let : Measure.IsOpenPosMeasure m := hfull.openPosMeasure
  exact fun x => (isClosed_le hf hg).closure_subset (m.dense_of_ae h x)

lemma continuous_dual_of_ball_averages [IsLocallyFiniteMeasure m] [IsUnifLocDoublingMeasure m]
    (hfull : FullSupport m) (f g : Lp ℝ 2 m) {F G : X → ℝ}
    (hF : Continuous F) (hG : Continuous G) (hFe : F =ᵐ[m] f) (hGe : G =ᵐ[m] g)
    {A : ℝ} (h : ∀ x y : X, ∀ r : ℝ,0 < r →
      (⨍ z in Metric.closedBall x r,f z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m) ≤
        A*(2*r+dist x y)^2) : ∀ x y,F x-G y ≤ A*dist x y^2 := by
  let : Measure.IsOpenPosMeasure m := hfull.openPosMeasure
  let S : Set X := {x | Tendsto (fun r : ℝ => ⨍ z in Metric.closedBall x r,f z ∂m) (𝓝[>] 0) (𝓝 (F x)) ∧
    Tendsto (fun r : ℝ => ⨍ z in Metric.closedBall x r,g z ∂m) (𝓝[>] 0) (𝓝 (G x))}
  have hS : ∀ᵐ x ∂m,x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average m ((Lp.memLp f).locallyIntegrable (by norm_num)) 1,
      IsUnifLocDoublingMeasure.ae_tendsto_average m ((Lp.memLp g).locallyIntegrable (by norm_num)) 1,hFe,hGe] with x hf hg heF heG
    constructor
    · rw [heF]
      apply hf (fun _ : ℝ => x) id tendsto_id
      filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using hr.le
    · rw [heG]
      apply hg (fun _ : ℝ => x) id tendsto_id
      filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using hr.le
  have HS : S ×ˢ S ⊆ {p : X×X | F p.1-G p.2 ≤ A*dist p.1 p.2^2} := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have H := le_of_tendsto_of_tendsto (hx.1.sub hy.2)
      (tendsto_const_nhds.mul (((tendsto_const_nhds.mul hr).add tendsto_const_nhds).pow 2))
      (show ∀ᶠ r in 𝓝[>] (0:ℝ),(⨍ z in Metric.closedBall x r,f z ∂m)-(⨍ z in Metric.closedBall y r,g z ∂m) ≤ A*(2*r+dist x y)^2 from by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact h x y r hr)
    change F x-G y ≤ A*dist x y^2
    simpa only [mul_zero,zero_add] using H
  have hclos : IsClosed {p : X×X | F p.1-G p.2 ≤ A*dist p.1 p.2^2} := isClosed_le (by fun_prop) (by fun_prop)
  exact fun x y => hclos.closure_subset (closure_mono HS ((m.dense_of_ae hS).prod (m.dense_of_ae hS) (x,y)))

variable [ProperSpace X] [SigmaFinite m]

lemma RCD.cheegerHeat_dual_pointwise {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m)
    {D E A : ℝ} (hfB : ∀ x,|f x| ≤ D) (hgB : ∀ x,|g x| ≤ E) (hA : 0 ≤ A)
    (hdual : ∀ x y,f x-g y ≤ A*dist x y^2)
    {t : ℝ} (ht : 0 ≤ t) {F G : X → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hFe : F =ᵐ[m] cheegerHeat h t (hf2.toLp f)) (hGe : G =ᵐ[m] cheegerHeat h t (hg2.toLp g)) :
    ∀ x y,F x-G y ≤ A*Real.exp (-2*K*t)*dist x y^2 := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let : IsUnifLocDoublingMeasure m := hrcd.1.uniform_local_doubling hN hfull hfin
  apply continuous_dual_of_ball_averages hfull _ _ hF hG hFe hGe
  intro x y r hr
  have hm (x : X) : m (Metric.closedBall x r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
  have hp (x : X) : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let u (x : X) := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hn (x : X) : ∀ᵐ z ∂m,0 ≤ u x z := setDensity_nonneg _ _ _
  have hmass (x : X) : ∫ z,u x z ∂m = 1 := setDensity_mass _ _ _ (hp x)
  have hb (x : X) : ∀ᵐ z ∂m,|u x z| ≤ (m (Metric.closedBall x r)).toReal⁻¹ := setDensity_bounded _ _ _
  have hs (x : X) : ∀ᵐ z ∂m,r < dist z x → u x z = 0 := setDensity_supported _ _ _ x (Subset.refl _)
  have H := hrcd.cheegerHeat_dual_pairing_balls hN hfull hfin h hf hg hf2 hg2 hfB hgB hA hdual
    (u x) (u y) (hn x) (hn y) (hmass x) (hmass y) (by positivity) (by positivity) (hb x) (hb y) x y hr.le hr.le (hs x) (hs y) ht
  have heq (x : X) (v : Lp ℝ 2 m) : ⟪v,u x⟫_ℝ = (⨍ z in Metric.closedBall x r,v z ∂m) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial]
    rw [setDensity_pairing,setAverage_eq,measureReal_def,smul_eq_mul]
  rw [heq x,heq y] at H
  simpa only [two_mul] using H

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [ProperSpace X] [SigmaFinite m] in
lemma heat_continuousVersion_bounded (hfull : FullSupport m) (h : QuadraticCheegerEnergy m)
    (f : Lp ℝ 2 m) {B : ℝ} (hB : 0 ≤ B) (hfb : ∀ᵐ x ∂m,|f x| ≤ B)
    {t : ℝ} (ht : 0 ≤ t) {F : X → ℝ} (hF : Continuous F)
    (hFe : F =ᵐ[m] cheegerHeat h t f) : ∀ x,|F x| ≤ B := by
  apply continuous_le_of_ae_le hfull hF.abs continuous_const
  filter_upwards [hFe,cheegerHeat_bounded h ht hB f hfb] with x hx hb
  simpa only [hx] using hb
end WeakHessian

end
end InlinedFile81

end OAI
