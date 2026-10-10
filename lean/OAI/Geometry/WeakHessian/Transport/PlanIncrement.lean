import Mathlib
import OAI.Geometry.WeakHessian.Transport.ScaledPlanYoung
import OAI.Geometry.WeakHessian.Transport.PlanHamiltonJacobiAction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

 def planMoment (π : Measure (Curve X)) (f : X → ℝ) (t : Time) : ℝ := ∫ γ, f (γ t) ∂π
 def planGradientEnergy (m : Measure X) (π : Measure (Curve X)) (f : X → ℝ) (t : Time) : ℝ :=
  ∫ γ, (weakGradient m f (γ t))^2 ∂π
 def planKineticCost (π : Measure (Curve X)) : ℝ := ∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma planGradientEnergy_nonneg (m : Measure X) (π : Measure (Curve X)) (f : X → ℝ) (t : Time) :
    0 ≤ planGradientEnergy m π f t := integral_nonneg fun _ => sq_nonneg _
omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma planKineticCost_nonneg (π : Measure (Curve X)) : 0 ≤ planKineticCost π :=
  integral_nonneg fun _ => sq_nonneg _

lemma IsTestPlan.plan_increment_bound (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {f : X → ℝ} (hf : LocalSobolev m f)
    (a b : Time) (hab : (a : ℝ) ≤ b) {M : ℝ}
    (hM : ∀ t : Time, (a : ℝ) ≤ t → (t : ℝ) ≤ b → planGradientEnergy m π f t ≤ M) :
    planMoment π f b-planMoment π f a ≤ ((b : ℝ)-a)/2*(M+planKineticCost π) := by
  by_cases he : a = b
  · subst b; simp
  have hab' : (a : ℝ) < b := lt_of_le_of_ne hab (fun h => he (Subtype.ext h))
  let : IsProbabilityMeasure π := hπ.1
  let c := (b : ℝ)-a
  have hc : 0 < c := sub_pos.mpr hab'
  let π' := π.map (WeakHessian.restrictCurve a b)
  have hp' : IsTestPlan m π' := hπ.restrictCurve a b hab'
  have hb' : BoundedTracks π' := hb.restrictCurve a b
  have hg' : ∀ᵐ γ ∂π', IsGeodesic γ :=
    continuous_ae_map_of_ae (continuous_restrictCurve a b) (hgeo.mono fun _ h => h.restrictCurve a b)
  have hD := (weakGradient_isMinimal hf.2).1
  have H := hD.geodesic_young_time_scaled hf.1.aemeasurable hp' hb' hg' hc timeOne (by norm_num [timeOne])
  have hleft : (∫ γ, f (γ timeOne)-f (γ timeZero) ∂π') =
      planMoment π f b-planMoment π f a := by
    rw [integral_sub (hf.1.integrable_eval hfin hp' hb' timeOne) (hf.1.integrable_eval hfin hp' hb' timeZero)]
    rw [integral_map (continuous_restrictCurve a b).measurable.aemeasurable
      (hf.1.integrable_eval hfin hp' hb' timeOne).1,
      integral_map (continuous_restrictCurve a b).measurable.aemeasurable
      (hf.1.integrable_eval hfin hp' hb' timeZero).1]
    simp only [restrictCurve_one,restrictCurve_zero,planMoment]
  have hcost : (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π') = c^2*planKineticCost π := by
    have hm : AEStronglyMeasurable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) π' :=
      (by fun_prop : Continuous (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2)).aestronglyMeasurable
    rw [integral_map (continuous_restrictCurve a b).measurable.aemeasurable hm,planKineticCost,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hgeo] with γ hγ
    rw [restrictCurve_zero,restrictCurve_one,hγ a b,abs_of_nonpos (sub_nonpos.mpr hab),mul_pow]
    dsimp only [c]
    ring
  have henergy : (∫ s in (0:ℝ)..1, ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π') ≤ M := by
    have hci := hp'.continuous_local_gradient_energy hfin hb' hf
    have HH := intervalIntegral.integral_mono_on (μ := volume) (show (0:ℝ) ≤ 1 by norm_num)
      (hci.intervalIntegrable 0 1) (intervalIntegrable_const (c := M)) ?_
    · simpa using HH
    intro s hs
    change (∫ γ, (weakGradient m f (γ (clampTime s)))^2 ∂π.map (WeakHessian.restrictCurve a b)) ≤ M
    rw [integral_map (continuous_restrictCurve a b).measurable.aemeasurable
      (hD.1.integrable_sq_eval hp' hb' (clampTime s)).1]
    change planGradientEnergy m π f (affineTime a b (clampTime s)) ≤ M
    apply hM
    · rw [coe_affineTime]
      have ht := (clampTime s).property.1
      nlinarith
    · rw [coe_affineTime]
      have ht := (clampTime s).property.2
      nlinarith
  rw [hleft,hcost] at H
  change planMoment π f b-planMoment π f a ≤ c/2*(M+planKineticCost π)
  change planMoment π f b-planMoment π f a ≤
    c/2*(∫ s in (0:ℝ)..1, ∫ γ, (weakGradient m f (evalReal γ s))^2 ∂π')+
      1/(2*c)*(c^2*planKineticCost π) at H
  calc
    _ ≤ _ := H
    _ ≤ c/2*M+1/(2*c)*(c^2*planKineticCost π) := by gcongr
    _ = _ := by field_simp

lemma lipschitzWith_clampTime : LipschitzWith 1 clampTime := by
  have h := (LipschitzWith.const (0:ℝ)).max ((LipschitzWith.const (1:ℝ)).min LipschitzWith.id)
  have he : max (0:ℝ≥0) (max 0 1) = 1 := by norm_num
  rw [he] at h
  exact h.subtype_mk _

lemma monotone_clampTime_coe : Monotone (fun t : ℝ => (clampTime t : ℝ)) :=
  monotone_const.max (monotone_const.min monotone_id)

lemma IsTestPlan.uniform_plan_increment (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {f : X → ℝ} (hf : LocalSobolev m f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a : ℝ, ∀ h : ℝ, 0 < h → h < δ →
      planMoment π f (clampTime (a+h))-planMoment π f (clampTime a) ≤
        h/2*(planGradientEnergy m π f (clampTime a)+ε+planKineticCost π) := by
  have hD := (weakGradient_isMinimal hf.2).1
  have hc : Continuous (planGradientEnergy m π f) :=
    hD.1.continuous_integral_sq_eval hfin hπ hb
  obtain ⟨δ,hδ,hUC⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  refine ⟨δ,hδ,?_⟩
  intro a h hh hhd
  have hab : (clampTime a : ℝ) ≤ clampTime (a+h) := monotone_clampTime_coe (by linarith)
  have hd : (clampTime (a+h) : ℝ)-(clampTime a : ℝ) ≤ h := by
    have H := lipschitzWith_clampTime.dist_le_mul (a+h) a
    simpa only [one_mul,NNReal.coe_one,Subtype.dist_eq,Real.dist_eq,add_sub_cancel_left,
      abs_of_nonneg hh.le,abs_of_nonneg (sub_nonneg.mpr hab)] using H
  have H := hπ.plan_increment_bound hfin hb hgeo hf (clampTime a) (clampTime (a+h)) hab
    (M := planGradientEnergy m π f (clampTime a)+ε) (by
      intro t hta htb
      have ht : dist t (clampTime a) < δ := by
        rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hta)]
        linarith
      have hu := hUC ht
      rw [Real.dist_eq,abs_lt] at hu
      linarith)
  apply H.trans
  gcongr
  exact add_nonneg (add_nonneg (planGradientEnergy_nonneg _ _ _ _) hε.le) (planKineticCost_nonneg _)

end WeakHessian

end
end

end OAI
